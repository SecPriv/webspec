(********************************************************************************)
(*  Copyright (c) 2022 Pedro Bernardo                                                *)
(*                                                                              *)
(*  Permission is hereby granted, free of charge, to any person obtaining a     *)
(*  copy of this software and associated documentation files (the "Software"),  *)
(*  to deal in the Software without restriction, including without limitation   *)
(*  the rights to use, copy, modify, merge, publish, distribute, sublicense,    *)
(*  and/or sell copies of the Software, and to permit persons to whom the       *)
(*  Software is furnished to do so, subject to the following conditions:        *)
(*                                                                              *)
(*  The above copyright notice and this permission notice shall be included in  *)
(*  all copies or substantial portions of the Software.                         *)
(*                                                                              *)
(*  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR  *)
(*  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,    *)
(*  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL     *)
(*  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER  *)
(*  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING     *)
(*  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER         *)
(*  DEALINGS IN THE SOFTWARE.                                                   *)
(*                                                                              *)
(********************************************************************************)

module type S =
sig
  (* RoundTrip-related functions*)
  val generate_scripts : States.VerifierState.t -> States.VerifierState.t
  val generate_sw : States.VerifierState.t -> States.sw_t -> string
end


module Script : S  =
struct
  let frame_indeces (dom : Types.DOM.t) : int list =
    List.fold_left (fun acc (idx, domel) -> (
      match (domel : Types.DOMElement.t option) with
      | Some(DOMElementResource (_url, el)) -> (
        match el with
        | ContentElementFrame (_fr, _html) -> (
          idx :: acc 
        )
        | _ -> acc
      )
      | _ -> acc

    ))
    []
    dom.dm_body

  let rec locate (idx : int) (target : int) (haystack : int list): int =
    let e = List.nth haystack idx in
    if e == target then
      idx
    else 
      locate (idx + 1) (target) (haystack)

  let rec does_target_exist (st : States.VerifierState.t) (path : Types.NestedDOMPath.t) (window : Types.Window.t) : bool =
    match path with 
    | DOMPath (hd :: tl, sel) -> (
        let trace = Option.get st.trace in
        let new_window = Model.Array.select trace.global.windows hd in
        does_target_exist st (DOMPath (tl, sel)) new_window
    )
    | DOMPath ([] , sel) -> (
      match sel with 
      | DOMTopLevel -> true
      | DOMIndex (idx) -> (
        (* before returning, check if the index is present in the dom*)
        let dom = window.wd_document.dc_dom.dm_body in
        let entry = List.assoc_opt idx dom in 
        Option.is_some entry
      )
    )

  let rec traverse_dompath (st : States.VerifierState.t) (path : Types.NestedDOMPath.t) (window : Types.Window.t) : Types.Window.t = 
    match path with
    | DOMPath(hd :: tl, selector) -> (
      let cel = Model.Array.select window.wd_document.dc_dom.dm_body hd in 
      let new_window = 
        match cel with 
        | Some(DOMElementResource (_, ContentElementFrame (frame, _html))) -> (
          let wd = frame.frame_window in 
          let trace = Option.get st.trace in
          let wind = Model.Array.select trace.global.windows wd  in
          wind
        )
        | _ -> failwith "index mismatch in dompath -> unable to retrieve iframe"
      in
      traverse_dompath st (DOMPath (tl, selector))  new_window 
    )
    | DOMPath ([], _ ) -> window

  let rec translate_dompath (st : States.VerifierState.t) (path : Types.NestedDOMPath.t) (window : Types.Window.t) (acc : int list) : int list =
    match path with
    | DOMPath (hd :: tl, selector) -> (
      (* look at the DOM and translate the index into the DOM to an index into the frames *)
      let idcs = frame_indeces window.wd_document.dc_dom in 
      let idcs = List.sort compare idcs in
      (* I am assuming it is here *)
      let idx = locate 0 hd idcs in
      
      let cel = Model.Array.select window.wd_document.dc_dom.dm_body hd in
      let new_window = 
        match cel with 
        | Some(DOMElementResource (_, ContentElementFrame (frame, _html))) -> (
          let wd = frame.frame_window in 
          let trace = Option.get st.trace in
          Model.Array.select trace.global.windows wd
        )
        | _ -> failwith "index mismatch in dompath -> unable to retrieve iframe"
      in
      translate_dompath st (DOMPath (tl, selector))  new_window (acc @ [idx])
    )
    | DOMPath ([] , sel) -> acc

  let rec get_frame_from_path (st : States.VerifierState.t) (path : int list) (trgt : Types.NestedDOMPath.t) (acc : string) : string = 
    match path with
    | [] -> acc 
    | hd :: tl -> (
      let acc = Printf.sprintf "%s.frames[%d]" acc hd in
      get_frame_from_path st tl trgt acc
    )

  let rec get_element_from_path (st : States.VerifierState.t) (path : int list) (trgt : Types.NestedDOMPath.t) (acc : string) : string = 
    match path with
    | [] -> (
      match trgt with
      | DOMPath (_, DOMIndex (i)) -> Printf.sprintf "%s.document.body.children[%d]" acc i
      | _ -> acc
    )
    | hd :: tl -> (
      let acc = Printf.sprintf "%s.frames[%d]" acc hd in
      get_element_from_path st tl trgt acc
    )
    
  let rec get_frame_from_path (st : States.VerifierState.t) (path : int list) (trgt : Types.NestedDOMPath.t) (acc : string) : string = 
    match path with
    | [] -> acc 
    | hd :: tl -> (
      let acc = Printf.sprintf "%s.frames[%d]" acc hd in
      get_frame_from_path st tl trgt acc
    )
  let rec get_frame_target (st : States.VerifierState.t) (path : int list ) (trgt : Types.NestedDOMPath.t) (acc : string) : string = 
    match path with
    | [] -> (
      match trgt with 
      | DOMPath (_, selector) -> 
        match selector with
        | DOMTopLevel -> acc
        | DOMIndex (idx) -> Printf.sprintf "%s.frames[%d]" acc idx
    )
    | hd :: tl -> (
      let acc = Printf.sprintf "%s.frames[%d]" acc hd in
      get_frame_target st tl trgt acc
    )

  let evscriptupdatehtml_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (w : Types.Window.t) (state : Types.State.t) (ass : int): States.VerifierState.t = 
    (* assuming it exists, get a list corresponding to the correct DOM path in window.frames *)
    let frame_path = translate_dompath st trgt w [] in 

    (* transform the frame_path into a string of accesses to window.frames *)
    let cmd = get_frame_from_path st frame_path trgt "top" in 

    (* determine if Trusted Types must be used *) 
    let trgt_wd = traverse_dompath st trgt w in
    let trgt_csp : Types.CSP.t option = trgt_wd.wd_document.dc_headers.rp_hd_csp in
    let trgt_tt = Option.bind trgt_csp (fun csp -> csp.csp_trusted_types) in 

    let src_wd = traverse_dompath st src w in
    let src_csp : Types.CSP.t option = src_wd.wd_document.dc_headers.rp_hd_csp in
    let src_tt = Option.bind src_csp (fun csp -> csp.csp_trusted_types) in 

    (* if target has ('require-trusted-types-for' 'script') and source has ('trusted-types' Some (policy)), then create a policy
       otherwise, ignore TT *)

    (* create if 
      target -> require, source None
      target -> requre, source Some (Some ()) *)

    let tt = 
      match src_tt, trgt_tt with
      | (None, Some({tt_policy= _ ; tt_require_for_script=true})) -> Some (Utils.rand_str 10)
      | (Some ({tt_policy=Some(Some(p)) ; tt_require_for_script=_}), Some({tt_policy=_ ; tt_require_for_script=true})) -> Some (string_of_int p)
      | _ -> None
    in

    let default_fmt_payload = Printf.sprintf ("(() => {\nlet new_el = '<div>%s</div>';\n%s\n})();") (* to make sure variables are not redeclared in future events *)
    in
    let tt_fmt_payload = Printf.sprintf ("(() => {const policy = trustedTypes.createPolicy('%s', {createHTML: input => input});\nlet new_el = policy.createHTML('<div>%s</div>');\n%s\n})(); ") 
    in

    (* add synchronization *)
    let asser = List.nth st.asserts_ordered ass in 
    let lock = States.VerifierState.get_wait_uuid st asser in

    let format_payload = 
      match tt with
      | Some(p) -> tt_fmt_payload p asser.value
      | None -> default_fmt_payload asser.value
    in

    if does_target_exist st trgt w then (
      let x = 
        match trgt with
        | DOMPath (_, DOMTopLevel) -> (
          (* should never happen *)
          failwith "Attempting to change a toplevel from an evscriptupdatehtml"
        )
        | DOMPath (_, DOMIndex (idx)) -> 
          [
            (Printf.sprintf "%s.document.body.children[%d].outerHTML = new_el;" 
              cmd idx ) ;
            (Printf.sprintf "StashUtils.putValue('%s', %s.document.body.children[%d].innerText );"
              asser.uuid cmd idx)
          ]
        
      in

      let x = format_payload @@ String.concat "\n" x in

      (* wrap x in a lock *)
      let x =
        match lock with 
        | Some(u) -> Printf.sprintf "StashUtils.takeValue(\'%s\').then(() => {\n%s\n});" u x
        | None -> x
      in

      let next = States.VerifierState.get_next_uuid st asser in
      (* trigger the next action *)
      let x = 
        match next with 
        | Some(u) -> (String.concat "\n" [x; (Printf.sprintf "StashUtils.putValue(\'%s\', 'dummy');" u)])
        | None -> x 
      in

      States.VerifierState.script_update_repr st src x 
    )
    else (
      let x = 
        match trgt with
        | DOMPath (_, DOMTopLevel) -> (
            failwith "Creating a page with an evscriptupdatehtml. Should never happen"
        )
        | DOMPath (_, DOMIndex (idx)) -> 
            [ 
              ( Printf.sprintf  "%s.document.body.innerHTML += new_el;" 
                    cmd ) ;
              ( Printf.sprintf "StashUtils.putValue('%s', %s.document.body.children[%s.document.body.children.length -1].innerText );"
                asser.uuid cmd cmd )
            ]
        
      in

      let x = format_payload @@ String.concat "\n" x in

      (* wrap x in a lock *)
      let x =
        match lock with 
        | Some(u) -> Printf.sprintf "StashUtils.takeValue(\'%s\').then(() => {\n%s\n});" u x
        | None -> x
      in

      (* trigger next if necessary *)
      let next = States.VerifierState.get_next_uuid st asser in
      let x = 
        match next with 
        | Some(u) -> (String.concat "\n" [x; (Printf.sprintf "StashUtils.putValue('%s', 'dummy');" u)])
        | None -> x 
      in

      States.VerifierState.script_update_repr st src x 
    )

  let evscriptdomainrelaxation_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (domain : Types.Domain.t) (state : Types.State.t) (ass : int): States.VerifierState.t =
    let asser = List.nth st.asserts_ordered ass in
    let lock = States.VerifierState.get_wait_uuid st asser in
    let next = States.VerifierState.get_next_uuid st asser in

    let lock_fmt = Option.value ~default:(Printf.sprintf "%s") (
      Option.bind lock (fun l -> Some (Printf.sprintf "StashUtils.takeValue('%s').then(() => {\n%s\n});" l))
    ) in


    let x = [ 
      Printf.sprintf "document.domain = '%s';" @@ Types.Domain.show domain ;
      Printf.sprintf "StashUtils.putValue('%s', document.domain);" asser.uuid ;
    ] in

    let x = Option.value ~default:x @@ 
      Option.bind next (fun n -> Some (x @ [Printf.sprintf "StashUtils.putValue('%s', 'dummy');" n]))
    in

    let x = lock_fmt @@ String.concat "\n" x in

    States.VerifierState.script_update_repr st src x 


  let evscriptsetcookie_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (c_idx : int) (sc : Types.SetCookie.t) (state : Types.State.t) (ass : int): States.VerifierState.t = 
    let asser = List.nth st.asserts_ordered ass in
    let lock = States.VerifierState.get_wait_uuid st asser in
    let next = States.VerifierState.get_next_uuid st asser in
    let cookie_v = Printf.sprintf "%s=%d" (Types.CookieName.show sc.sc_name) (sc.sc_value) in

    let lock_fmt = Option.value ~default:(Printf.sprintf "%s") (
      Option.bind lock (fun l -> Some (Printf.sprintf "StashUtils.takeValue('%s').then(() => {\n%s\n});" l))
    ) in

    let frame_path = translate_dompath st trgt state.st_window [] in 
    (* transform the frame_path into a string of accesses to window.frames *)
    let cmd = get_frame_target st frame_path trgt "top" in 

    let x = [ 
      Printf.sprintf "%s.document.cookie = '%s';" cmd @@ Types.SetCookie.show sc ;
      Printf.sprintf "StashUtils.putValue('%s', (() => {let vv = %s.document.cookie.match('%s'); return vv ? vv[0] : 'error'})());" asser.uuid cmd cookie_v;
    ] in

    let x = Option.value ~default:x @@ 
      Option.bind next (fun n -> Some (x @ [Printf.sprintf "StashUtils.putValue('%s', 'dummy');" n]))
    in

    let x = lock_fmt @@ String.concat "\n" x in

    States.VerifierState.script_update_repr st src x


  let evscriptnavigateframe_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (dst : Types.NestedDOMPath.t) (frm : Types.Frame.t) (loc : Types.URL.t) (state : Types.State.t) (ass : int): States.VerifierState.t = 
    let window = state.st_window in

    let frame_path = translate_dompath st dst window [] in 
    (* transform the frame_path into a string of accesses to window.frames *)
    let cmd = get_frame_target st frame_path dst "top" in 

    let script = Types.NestedDOMPath.Map.find src st.scripts in 
    let st = States.VerifierState.update_url_sources st loc (Some(HTMLScript (script.url))) in

    let asser = List.nth st.asserts_ordered ass in

    (* if blob url, get the current uuid and advance the counter *)
    let format_payload = 
      match loc.url_protocol, loc.url_path with
      | ProtocolBlob, Coq_url_path_blob (_, i) -> (
        let uuid = States.VerifierState.blob_current_uuid st loc i in
        (* async so I can only write after I changed the location. Otherwise the script will stop running*)
        Printf.sprintf "StashUtils.takeValue('%s').then(async (t_url) => {\n%s\n})"
          uuid 
      )
      | _ -> Printf.sprintf "let t_url = '%s';\n%s\n" @@ Types.URL.show @@ States.VerifierState.translate_url st loc
    in


    (* advance the uuid index for this blob if we are using a blob url *)
    let st = 
      match loc.url_protocol, loc.url_path with
      | ProtocolBlob, Coq_url_path_blob (_, i) -> States.VerifierState.blob_next_uuid st loc i
      | _ -> st
    in

    let inner = [
      (* satisfy the assertion first *)
      Printf.sprintf "await StashUtils.putValue('%s', '%s');" asser.uuid asser.value ;
      Printf.sprintf  "%s.location = t_url;" cmd
    ] in

    let x = format_payload @@ String.concat "\n" inner in

    let lock = States.VerifierState.get_wait_uuid st asser in
    let next = States.VerifierState.get_next_uuid st asser in


    (* trigger the next before , because we might not be running after (??) *)
    let x = Option.value ~default:x (
      Option.bind next (fun n -> Some (String.concat "\n" [Printf.sprintf "StashUtils.putValue('%s', 'dummy');" n ; x]))
    ) in

    let lock_fmt = Option.value ~default:(Printf.sprintf "(() => {\n%s\n})();") (
      Option.bind lock (fun l -> Some (Printf.sprintf "StashUtils.takeValue('%s').then(() => {\n%s\n});" l))
    ) in

    States.VerifierState.script_update_repr st src @@ lock_fmt x
  
  let evscriptpostmessage_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (url : Types.URL.t option) (state : Types.State.t) (ass : int): States.VerifierState.t = 
    st
  
  let evscriptcreatebloburl_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (url : Types.URL.t) (state : Types.State.t) (ass : int): States.VerifierState.t =
    let blob = States.VerifierState.blobstore_get_blob st url @@ Some(state) in 
    let blob_internal = States.VerifierState.blob_get st url @@ States.VerifierState.blobstore_get_index st url in
    let asser = List.nth st.asserts_ordered ass in

    let ctype = 
      match blob.blob_celt with
      | ContentElementHTML (_)
      | ContentElementFrame (_, _) -> "text/html"
      | ContentElementImage (_) -> "image/bmp"
      | ContentElementScript (_) -> "application/x-javascript"
      
    in

    let checklist = 
      match st.creator_blob with 
      | Some(c_url) -> (
        if url = c_url then (
          Some(st.csp_check_urls)
        ) else (
          None
        )
      )
      | None -> None 
    in

    let html = 
      match blob.blob_celt with
      | ContentElementHTML (html)
      | ContentElementFrame (_, html) -> Html.Translator.html_to_string st html checklist
      | ContentElementImage (_) -> "TODO: HARDCODED IMAGE BYTES"
      | _ -> failwith "[evscriptcreatebloburl_handler] Trying to create a blob with javascript"
    in


    let vv = (Base64.encode_exn html) in
    let st = States.VerifierState.assert_change st ass vv true in
    
    let x = [
      Printf.sprintf "let b = new Blob([\"%s\"], {type: '%s'});" html ctype ;
      Printf.sprintf "let u = URL.createObjectURL(b);" ;
      Printf.sprintf "b.text().then((v) => { StashUtils.putValue('%s', btoa(v)); });" asser.uuid;
    ] in


    let x = List.fold_left (fun acc uuid -> acc @ [Printf.sprintf "StashUtils.putValue('%s', u);" uuid]) 
      x blob_internal.uuids
    in

    let lock = States.VerifierState.get_wait_uuid st asser in
    let next = States.VerifierState.get_next_uuid st asser in


    let x = Option.value ~default:x (
      Option.bind next (fun n -> Some (x @ [Printf.sprintf "StashUtils.putValue('%s', 'dummy');" n]))
    ) in

    let lock_fmt = Option.value ~default:(Printf.sprintf "(() => {\n%s\n})();") (
      Option.bind lock (fun l -> Some (Printf.sprintf "StashUtils.takeValue('%s').then(() => {\n%s\n});" l))
    ) in

    let x = lock_fmt @@ String.concat "\n" x in

    States.VerifierState.script_update_repr st src x


  let evscriptstoragesetitem_handler (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (url : Types.Origin.t) (k : int) (v : int) (state : Types.State.t) (ass : int): States.VerifierState.t =
    st

  let evscriptupdatecache (st : States.VerifierState.t) (src : Types.NestedDOMPath.t) (rq : int) (rp : int option) (state : Types.State.t) (ass : int): States.VerifierState.t =
    (* to know which cache I should use, need to get the correct one based on my origin. 
       This can be done via the rq url since we know SWs can only match against their origin*)
    let trace = Option.get st.trace in
    let req = Model.Array.select trace.global.requests rq in
    let url = States.VerifierState.translate_url st req.rq_url in
    let og = Model.Browser.TupleOrigin (url.url_protocol, url.url_host, url.url_port) in
    let sw = try List.find (fun (x : States.sw_t) -> (compare x.origin og) = 0 ) st.sws with
      Invalid_argument _ -> failwith ("ServiceWorker not associated with the given origin " ^ (Types.Origin.show og))
    in
 
    (* generate the lock code if necessary *)
    let asser = List.nth st.asserts_ordered ass in 
    let lock = States.VerifierState.get_wait_uuid st asser in
    print_endline ("ServiceWorker is using cache: " ^ sw.cache) ;


    let format_payload = Option.value ~default:(Printf.sprintf "%s")
      (Option.bind lock (fun uuid -> Some(Printf.sprintf "StashUtils.takeValue('%s').then(() => {\n%s\n});" uuid)))
    in

    (* generate the request and response events *)
    let s_req = Serviceworker.ServiceWorker.s_request st rq in
    let s_resp = Option.bind rp (fun i -> Some(Serviceworker.ServiceWorker.s_response st i)) in 

    (* Cache.add(request) if rp is None, then it's a cache.add. Otherwise it's a cache.put*)
    let x =
      match s_resp with 
      | None -> [ 
        format_payload @@ 
        Printf.sprintf 
        "caches.open('%s').then((mycache) => { 
          mycache.add(%s).then(() => { StashUtils.putValue('%s', '%s');})
          .catch(() => { StashUtils.putValue('%s', 'false'); });
        });"
        sw.cache
        s_req 
        asser.uuid
        asser.value
        asser.uuid
        ]
      | Some(rresp) -> [ 
        format_payload @@ 
        Printf.sprintf
        "caches.open('%s').then((mycache) => { 
          mycache.put(%s, %s).then(() => { StashUtils.putValue('%s', '%s');})
          .catch(() => { StashUtils.putValue('%s', 'false'); });
        });"
        sw.cache
        s_req
        rresp
        asser.uuid
        asser.value
        asser.uuid
      ]
    in

    let next = States.VerifierState.get_next_uuid st asser in

    let x = Option.value ~default:x ( Option.bind next (fun uuid -> Some(x @ [Printf.sprintf "StashUtils.putValue('%s', 'dummy');" uuid])) )
    in

    States.VerifierState.script_update_repr st src @@ String.concat "\n" x


  let handle_ev (st : States.VerifierState.t) ( p : (Types.Event.t * Types.State.t * int)) : States.VerifierState.t = 
    let (ev, state, ass) = p in 
    match ev with
    | EvScriptUpdateHTML (src,trgt, w) ->( print_endline "EvScriptUpdateHTML"; evscriptupdatehtml_handler st src trgt w state ass)
    | EvScriptDomainRelaxation (src, domain) ->( print_endline "EvScrptDomainRelaxation" ; evscriptdomainrelaxation_handler st src domain state ass) 
    | EvScriptUpdateCache (src, rq, rp) ->( print_endline "EvScriptUdateCache" ; evscriptupdatecache st src rq rp state ass) 
    | EvScriptSetCookie (pt, ctx, idx, sc) ->( print_endline "EvScriptSetCookie" ; evscriptsetcookie_handler st pt ctx idx sc state ass) 
    | EvScriptNavigateFrame (src, dst, frm, loc) ->( print_endline "EvScriptNavigateFrame" ; evscriptnavigateframe_handler st src dst frm loc state ass) 
    | EvScriptPostMessage (src, trgt, url) ->( print_endline "EvScriptPostMessage" ; evscriptpostmessage_handler st src trgt url state ass) 
    | EvScriptCreateBlobUrl (src, url) ->( print_endline "EvScriptCreateBlobUrl" ; evscriptcreatebloburl_handler st src url state ass) 
    | EvScriptStorageSetItem (src, og, k, v) ->( print_endline "EvScriptStorageSetItem" ; evscriptstoragesetitem_handler st src og k v state ass)
    | _ -> st

  let generate_script (st : States.VerifierState.t) (src : Types.NestedDOMPath.t ): States.VerifierState.t = 
    let script = Types.NestedDOMPath.Map.find src st.scripts in
    List.fold_left handle_ev st script.events

  let generate_scripts (st : States.VerifierState.t) : States.VerifierState.t =
    let scripts = st.scripts in 

    Types.NestedDOMPath.Map.fold (fun k v acc -> ( generate_script acc k)) scripts st

  
  let generate_sw (st : States.VerifierState.t) (sw : States.sw_t) : string = 
    let trace = Option.get st.trace in

    (* 1. create filename with origin and a prefix
       2. create the url to be returned with a query paramenter specific to sws
       3. loop through events(
        - if updatecache -> ignore for now
        - if cachematch -> get a list of assertions
       4. Call the templating engine to generate the files
       5. Return the filenme *)

    let t_origin = States.VerifierState.translate_origin st sw.origin in

    let worker_name = 
      match t_origin with 
      | TupleOrigin (proto, domn, port) -> (
        Printf.sprintf "%s.%s.%s_sw"
        (Types.Protocol.show proto)
        (Types.Domain.show @@ Option.value ~default:(Coq_domain (9999)) domn)
        (string_of_int @@ Option.get port)
      )
      | _ -> failwith "Service worker cannot be registered in an opaque origin (?)"
    in

    let url = Printf.sprintf "%s/verifier/server.py?sw=1"  @@ Types.Origin.show t_origin in


    let install = Jingoo.Jg_template.from_file "templates/install.jingoo" ~models:[
      ("worker", Jingoo.Jg_types.Tstr worker_name) ;
    ] in

    Utils.write_to_file ("output/" ^ worker_name ^ ".html") install ; 

    let asserts : Jingoo.Jg_types.tvalue list = 
      List.fold_left (fun acc ((e, tst, i) : (Types.Event.t * Types.State.t * int)) -> (
        match e with
        | EvWorkerCacheMatch (rp_idx) -> (

          let rp = Model.Array.select trace.global.responses rp_idx in
          let rp_url = Types.URL.show @@ States.VerifierState.translate_url st rp.rp_url in

          let ass = List.nth st.asserts_ordered i in
          let next = States.VerifierState.get_next_uuid st ass in

          print_endline ("how many assertions " ^ string_of_int @@ List.length st.asserts_ordered);

          acc @ [Jingoo.Jg_types.Tobj [ 
            ("url", Jingoo.Jg_types.Tstr rp_url) ;
            ("uuid", Jingoo.Jg_types.Tstr ass.uuid) ;
            ("val", Jingoo.Jg_types.Tstr ass.value) ; 
            ("lock", Jingoo.Jg_types.Tstr ass.lock) ; 
            ("next", match next with | None -> Jingoo.Jg_types.Tnull | Some(n) -> Jingoo.Jg_types.Tstr n)
          ]]
        )
        | _ -> acc 
      )) [] sw.events
    in

    let sw_repr = 
      Jingoo.Jg_template.from_file "templates/sw.jingoo" ~models:[
        ("cache", Jingoo.Jg_types.Tstr sw.cache) ; 
        ("asserts", Jingoo.Jg_types.Tlist asserts) ;
        ("cupdates", Jingoo.Jg_types.Tlist []);
      ]
    in

    Utils.write_to_file ("output/" ^ worker_name ^ ".js") sw_repr ; 

    url

end  
