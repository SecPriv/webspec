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

module type Visitor =
sig
  type t

  val request_handler :  t -> Model.Browser.coq_Emitter -> Model.Browser.coq_Request -> int -> Types.State.t option -> t

  val response_handler : t -> Model.Browser.coq_Response -> int -> t

  val url_source_handler : t -> Model.Browser.coq_URL-> Model.Browser.coq_HTMLElement option -> t 

  val url_handler : t -> Model.Browser.coq_URL -> t

  val domupdate_handler : t -> Types.NestedDOMPath.t -> t 

  val default_handler : t -> Model.Browser.coq_Event -> t

  val handle : t -> (Types.Event.t * Types.State.t option) -> t

end 


module Preprocessor : Visitor with type t = States.VerifierState.t =
struct
  type t = States.VerifierState.t

  let default_handler (st : t) (_ev : Types.Event.t) : t = 
    st

  let domain_handler (st : t)  (domain : Types.Domain.t) : t =
    States.VerifierState.update_domains  st domain

  let port_handler (st : t)  (protocol : Types.Protocol.t) (port : int) : t =
    States.VerifierState.update_ports  st protocol port

  let origin_handler (st : t)  (rq_proto : Types.Protocol.t) 
      (rq_domain : Types.Domain.t option) (rq_port : int option) : t =

    match rq_domain with
    | None -> st (* opaque origin *)
    | Some(domain) -> (
        let st = States.VerifierState.update_origins  st (Model.Browser.TupleOrigin (rq_proto, Some(domain), rq_port)) in
        domain_handler  st domain
      )

  let url_handler (st : t) (rq_URL : Model.Browser.coq_URL) : t = 
    let { url_protocol=proto; url_host=domain;
          url_port=port ; url_path=path } : Model.Browser.coq_URL = rq_URL in
            
    (* Opaque origins are null *)
    match proto, path with
    | ProtocolData, Coq_url_path_data (nonce, content_idx) -> (
        let st = States.VerifierState.update_urls  st rq_URL in
        match port with
        | Some (v) -> port_handler  st proto v
        | _ -> st
      )
    | ProtocolBlob, Coq_url_path_blob (origin, content_idx) -> (
        let st = match origin with
          | TupleOrigin (o_proto, o_domain, o_port) -> (
            let st' = origin_handler st o_proto o_domain o_port in 
            Option.value ~default:st' (Option.bind o_port (fun p -> Some(port_handler st o_proto p)))
            )
          | OpaqueOrigin (nonce) -> st
          (* the case for about blank *)
        in
        let st = States.VerifierState.update_urls  st rq_URL in 

        match port with 
        | Some (v) -> port_handler  st proto v
        | _ -> st
      )
    | _, Coq_url_path_res (_) -> (
      let st = origin_handler  st proto domain port in
      let st = States.VerifierState.update_urls  st rq_URL in
      match port with 
      | Some (v) -> port_handler  st proto v
      | _ -> st
    )
    | _ -> st (* malformed url, will be ignored by the browser. Do nothing *)


  let request_handler (st : t) (emitter: Types.Emitter.t) (request : Types.Request.t) (nonce : int) (tst : Types.State.t option) : t =
    let { rq_method; rq_url=url;
          rq_headers=hdrs; rq_body=body } : Model.Browser.coq_Request = request in

    let st = url_handler st url in

    let st =
      match emitter with
      | EmitterScript (path, _scr) -> (
        match tst with
        | Some (ttst) -> (
          let st = States.VerifierState.script_update st path (EvRequest (emitter, request, nonce)) ttst (-1) in 
          let x = (Printf.sprintf " fetch('%s')" (Types.URL.show @@ States.VerifierState.translate_url st url)) in 
          States.VerifierState.script_update_repr st path x 
        )
        | _ -> failwith "state not available for request with emitter script"
      )
      | _ -> st
    in



    let source = Types.URL.Map.find_opt url st.url_sources in

    match source with
    | Some(_) -> (
       st
    )
    | None -> (
      (* no source, it is an action I have to perform *)
      match emitter with 
      | EmitterClient -> (
        let vv = "irrelevant" in 
        let uuid = Uuid.Generator.gen_uuid () in 
        (* let st = States.VerifierState.uuid_next st in *)
        let st = States.VerifierState.assert_add st uuid vv true in

        let assert_idx = (List.length st.asserts_ordered) - 1 in 
        let repr = Printf.sprintf "window.open('%s');" (Types.URL.show (States.VerifierState.translate_url st url)) in
        let bloburl = 
          match url.url_protocol with
          | ProtocolBlob -> Some(url)
          | _ -> None
        in
        (* here, add a blob uuid if we need to get it first *)
        let st = 
          match url with 
          | {url_protocol=ProtocolBlob; url_host=_; url_port=_; url_path=(Coq_url_path_blob (_, i))} ->
              States.VerifierState.blob_uuid_add st url i
          | _ -> st
        in
        States.VerifierState.action_add st repr assert_idx bloburl
      )
      | EmitterScript (src, script) -> (
        st
      )
      | EmitterForm (src, form) -> (
        st
      )
      | EmitterWorker -> ( st )
      | EmitterCORSPreflight (_nonce, _req) -> ( st )
    )


  let url_source_handler (st : t) (url : Types.URL.t) (src : Types.HTMLElement.t option) : t = 
    States.VerifierState.update_url_sources  st url src

  let accumulate_urls (st : t) (element: (int * Model.Browser.coq_HTMLElement option)) : t = 
    match element with
    | (_, Some(HTMLImage (url))) -> (
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLImage(url)))
    )
    | (_, Some(HTMLScript (url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLScript(url)))
   )
    | (_, Some(HTMLForm (mtd, url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLForm(mtd, url)))
   ) (* for Forms we will see an EmitterForm event later*)
    | (_, Some(HTMLFrame (url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLFrame(url)))
   )
    | _ -> st


  let htmlbody_handler (st : t) (body : Model.Browser.coq_HTMLBody) : t =
    (* Utils.array_rec_iter st accumulate_urls body *)
    List.fold_left accumulate_urls st body

  let html_handler (st : t)  (html : Model.Browser.coq_HTML) : t = 
    htmlbody_handler st html.html_body


  let response_headers_handler (st : t) (rheaders : Types.ResponseHeaders.t) : t = 
    let st = match rheaders.rp_hd_set_cookie with
      | None -> st
      | Some(hd) -> match hd.sc_domain with | None -> st | Some(d) -> domain_handler st d 
    in
    let st = match rheaders.rp_hd_access_control_allow_origin with
      | Some(TupleOrigin (prot, d, p)) -> origin_handler st prot d p
      | _ -> st
    in
    let st = match rheaders.rp_hd_location with
      | None -> st
      | Some(url) -> url_handler st url 
    in
    match rheaders.rp_hd_csp with
      | None -> st
      | Some(csp) -> (
        match csp.csp_script_src with 
        | Some(CSPSrcSource (proto, subd, dom, port, path)) -> (
            let st =
              match port with 
            | None -> st
            | Some(p) -> port_handler st (Option.value ~default:ProtocolHTTP proto) p 
            in 
            match subd with 
            | None 
            | Some(None) -> domain_handler st (Coq_domain(dom))
            | Some(Some(sd)) -> domain_handler st (Coq_subdomain(sd, dom))
          )
        | _ -> st 
      )

  let response_handler (st : t) (response : Model.Browser.coq_Response) (nonce : int) : t =
    let { rp_url=url; rp_code=code; rp_headers=headers ; rp_content=content} : Model.Browser.coq_Response = response in

    (* check if the request exists *)

    let st = 
      match Types.Int.Map.mem nonce st.request with
      | true -> st
      | false -> (
        assert (nonce == 0) ; 
        let trace = Option.get st.trace in
        let req = Model.Array.select trace.global.requests 0 in
        let ev_req = Model.Browser.EvRequest (EmitterClient, req, 0) in 
        let st = States.VerifierState.add_request st ev_req in 
        request_handler st EmitterClient req 0 None
      )
    in

    let st = response_headers_handler st headers in 

    match content with 
    | Some (ContentElementHTML (html)) -> html_handler  st html
    | Some (ContentElementImage (url)) -> (
      url_handler st url
    )
    | Some (ContentElementScript (script)) -> (
      url_handler st script.script_src
    )
    | Some (ContentElementFrame (frame, html)) -> (

      let st = url_handler st frame.frame_src in 
      html_handler st html 
    (* visit html *)
    )
    | _ -> st


  let domupdate_handler (st : t) (path : Types.NestedDOMPath.t) : t = 
    let corr = List.hd st.correlators in

    let response : (Types.Response.t option) = States.VerifierState.find_response_opt st corr in

    match response  with
    | Some (r : Types.Response.t) -> (
      let ctype = r.rp_headers.rp_hd_content_type in 
      match ctype with
      | Some(ContentTypeScript) -> States.VerifierState.script_add st path corr
      | _ -> st
    )
    | _ -> st



  let evscriptupdatehtml_handler (st : t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (w : Types.Window.t) (tst : Types.State.t option): t = 

    (* create_assertion *)
    let vv = Utils.rand_str 10 in

    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    match tst with
    | Some(ttst) -> (
      States.VerifierState.script_update st src (EvScriptUpdateHTML (src, trgt, w)) ttst assert_idx
    )
    | _ -> failwith "mising state for EvScriptUpdateHtml"
    

  let evscriptdomainrelaxation_handler (st : t) (src : Types.NestedDOMPath.t) (domain : Types.Domain.t) (tst : Types.State.t option) : t =

    let vv = (Types.Domain.show domain) in
    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    match tst with
    | Some(ttst) -> (
        States.VerifierState.script_update st src (EvScriptDomainRelaxation (src, domain)) ttst assert_idx
    )
    | _ -> failwith "mising state for EvScriptDomainRelaxation"

  let evscriptsetcookie_handler (st : t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (c_idx : int) (sc : Types.SetCookie.t) (tst : Types.State.t option): t = 

    let cm : Types.CookieMapping.t = { cm_name=sc.sc_name; cm_value=sc.sc_value } in
    let vv = (Types.CookieMapping.show cm) in
    let uuid = Uuid.Generator.gen_uuid () in 
    (* let st = States.VerifierState.uuid_next st in *)
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    match tst with
    | Some(ttst) -> (
        States.VerifierState.script_update st src (EvScriptSetCookie (src, trgt, c_idx, sc)) ttst assert_idx
    )
    | _ -> failwith "mising state for EvScriptDomainRelaxation"

  let evscriptnavigateframe_handler (st : t) (src : Types.NestedDOMPath.t) (dst : Types.NestedDOMPath.t) (frm : Types.Frame.t) (loc : Types.URL.t) (tst : Types.State.t option) : t = 
    let vv = Utils.rand_str 10 in
    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in
    let st =
      match loc.url_protocol with
      | ProtocolBlob -> States.VerifierState.blob_uuid_add st loc @@ States.VerifierState.blobstore_get_index st loc 
      | _ -> st 
    in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    let st =
      match tst with
      | Some(ttst) -> (
        States.VerifierState.script_update st src (EvScriptNavigateFrame (src, dst, frm, loc)) ttst assert_idx
      )
      | _ -> failwith "mising state for EvScriptNavigateFrame" 
    in
    url_source_handler st loc None
  
  let evscriptpostmessage_handler (st : t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (url : Types.URL.t option) : t = 
    st
  
  let evscriptcreatebloburl_handler (st : t) (src : Types.NestedDOMPath.t) (url : Types.URL.t) (tst : Types.State.t option): t =
    let blob_idx = States.VerifierState.blobstore_get_index st url in
    let st = States.VerifierState.blob_add st url blob_idx in
    let vv = "TEMP" in 
    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    match tst with
    | Some(ttst) -> (
      States.VerifierState.script_update st src (EvScriptCreateBlobUrl (src, url)) ttst assert_idx
    )
    | _ -> failwith "mising state for EvScriptCreateBlobURL" 

  let evscriptstoragesetitem_handler (st : t) (src : Types.NestedDOMPath.t) (url : Types.Origin.t) (k : int) (v : int) : t =
    st

  let evscriptupdatecache (st : t) (src : Types.NestedDOMPath.t) (rq : int) (rp : int option) (tst : Types.State.t option): t =
    let rp = Option.get rp in (* might lead to errors; check for the case where there is no rp (does it mean cleaning the cache?) *)
    
    let vv = "true" in
    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    match tst with
    | Some(ttst) -> (
      States.VerifierState.script_update st src (EvScriptUpdateCache (src, rq, Some(rp))) ttst assert_idx
    )
    | _ -> failwith "mising state for EvScriptUpdateCache"


  let evworkercachematch (st : t) (rp : int) (tst : Types.State.t option) : t = 
    let trace = Option.get st.trace in
    let resp = Model.Array.select trace.global.responses rp in 

    let url = States.VerifierState.translate_url st resp.rp_url in
    let origin = Model.Browser.TupleOrigin (url.url_protocol, url.url_host, url.url_port) in 
    

    let vv = (Types.URL.show url) in
    let uuid = Uuid.Generator.gen_uuid () in 
    let st = States.VerifierState.assert_add st uuid vv true in

    let assert_idx = (List.length st.asserts_ordered) - 1 in 

    let tst = try Option.get tst with
      Invalid_argument _ -> failwith "EvWorkerCacheMatch: State not present"
    in

    let st = States.VerifierState.service_worker_update st origin (EvWorkerCacheMatch rp) tst assert_idx in 
    st

  let evworkerupdatecache (st : t) (rq : int) (rp : int) (tst : Types.State.t option) : t = 
    st


  let handle (st : t)  ( p : (Types.Event.t * Types.State.t option)) : t = 
    let (ev, state) = p in 
    match ev with
    | EvInit -> ( print_endline "EvInit" ; st )
    | EvRequest (em, req, nonce) -> (print_endline  ("EvRequest " ^ (string_of_int nonce)) ; let st = States.VerifierState.add_request st ev in request_handler st em req nonce state )
    | EvResponse (resp, nonce) -> (print_endline ("EvResponse " ^ (string_of_int nonce))  ; let st = States.VerifierState.add_response st ev in response_handler st resp nonce )
    | EvDOMUpdate path -> ( print_endline "EvDOMUpdate" ; domupdate_handler st path ) 
    | EvScriptUpdateHTML (src,trgt, w) ->( print_endline "EvScriptUpdateHTML"; evscriptupdatehtml_handler st src trgt w state)
    | EvScriptDomainRelaxation (src, dmn) ->( print_endline "EvScrptDomainRelaxation" ; evscriptdomainrelaxation_handler st src dmn state ) 
    | EvWorkerCacheMatch rp -> ( print_endline "EvWorkerCacheMatch" ; evworkercachematch st rp state ) 
    | EvWorkerUpdateCache (rq, rp) ->( print_endline "EvWorkerUpdateCache" ; evworkerupdatecache st rq rp state) 
    | EvScriptUpdateCache (src, rq, rp) ->( print_endline "EvScriptUdateCache" ; evscriptupdatecache st src rq rp state) 
    | EvScriptSetCookie (src, trgt, c_idx, sc) ->( print_endline "EvScriptSetCookie" ; evscriptsetcookie_handler st src trgt c_idx sc state ) 
    | EvScriptNavigateFrame (src, dst, frm, loc) ->( print_endline "EvScriptNavigateFrame" ; evscriptnavigateframe_handler st src dst frm loc state ) 
    | EvScriptPostMessage (_, _, _) ->( print_endline "EvScriptPostMessage" ; st ) 
    | EvScriptCreateBlobUrl (src, url) ->( print_endline "EvScriptCreateBlobUrl" ; evscriptcreatebloburl_handler st src url state) 
    | EvScriptStorageSetItem (_, _, _, _) ->( print_endline "EvScriptStorageSetItem" ; st )
end


module ResponseGenerator : Visitor with type t = States.VerifierState.t =
struct
  type t = States.VerifierState.t

  let default_handler (st : t) (_ev : Types.Event.t) : t = 
    st

  let domain_handler (st : t)  (domain : Types.Domain.t) : t =
    st

  let port_handler (st : t)  (protocol : Types.Protocol.t) (port : int) : t =
    st

  let origin_handler (st : t)  (rq_proto : Types.Protocol.t) =
    st

  let url_handler (st : t) (rq_URL : Model.Browser.coq_URL) : t = 
    st

  let request_handler (st : t) (emitter : Types.Emitter.t) (request : Types.Request.t) (nonce : int) (tst : Types.State.t option): t =
    st

  let url_source_handler (st : t) (url : Types.URL.t) (src : Types.HTMLElement.t option) : t = 
    st

  let accumulate_urls (st : t) (element: (int * Model.Browser.coq_HTMLElement option)) : t = 
    match element with
    | (_, Some(HTMLImage (url))) -> (
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLImage(url)))
    )
    | (_, Some(HTMLScript (url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLScript(url)))
   )
    | (_, Some(HTMLForm (mtd, url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLForm(mtd, url)))
   ) (* for Forms we will see an EmitterForm event later*)
    | (_, Some(HTMLFrame (url))) -> (
        
        let st = url_handler  st url in 
        url_source_handler  st url (Some(HTMLFrame(url)))
   )
    | _ -> st


  let htmlbody_handler (st : t) (body : Model.Browser.coq_HTMLBody) : t =
    List.fold_left accumulate_urls st body

  let html_handler (st : t)  (html : Model.Browser.coq_HTML) : t = 
    htmlbody_handler st html.html_body

  let add_report_uri (json : Yojson.Safe.t) (no_csp : bool) : Yojson.Safe.t = 
    let report_uri = "report-uri https://web-platform.test:8443/verifier/csp.py" in
    if no_csp then (
      failwith "[add_report_uri] no_csp: UNIMPLEMENTED"
      (* json *)
    ) else (
      match json with 
      | `Assoc ([("code", c) ; ("headers", `Assoc lst) ]) -> (
        `Assoc ( 
          [ ("code", c) ;
            ("headers", `Assoc (
              List.map 
              (fun (k, v) -> if k = "Content-Security-Policy" then ( 
                  (k, `String (Printf.sprintf "%s %s" (List.fold_left (fun acc x -> if x = (Char.chr 34) then acc else acc ^ (Char.escaped x)) 
                  "" @@ List.of_seq @@ String.to_seq (Yojson.Safe.pretty_to_string v))  report_uri))
                ) else ((k,v))
              ) 
              lst 
              )
            )
          ]
        )
      )
      | _ -> failwith "[add_report_uri] not the right ResponseHeaders json format"
    )

  let response_handler (st : t) (response : Model.Browser.coq_Response) (nonce : int): t =
    let { rp_url=url; rp_code=code; rp_headers=headers ; rp_content=content} : Model.Browser.coq_Response = response in

    match url.url_protocol with 
    | ProtocolData
    | ProtocolBlob -> (* do nothing, as there are no responses from the server *) st
    | _ -> (
      (* PROTO CODE *)

      let code = Types.ResponseCode.show code in

      (* 1. generate the headers *)
      (* let headers = Types.ResponseHeaders.show headers in *)

      let corr = States.VerifierState.find_response_r st response in 
      let corr = match corr with 
      | Some(c) -> c
      | None -> failwith "Abort: Response without a causing request."
      in 

      let req = States.VerifierState.find_request st corr
      in

      let mthd = Types.RequestMethod.show req.rq_method in 
      let turl = States.VerifierState.translate_url st url in 

      (* match on the protocol to extract the domain *)
      (* data urls will not have a domain, and that's fine*)
      let domain = 
        match turl.url_host with
        | Some(d) -> d
        | None -> Coq_domain (0) (* failwith "request with response should always have a domain" *)
      in
      let port = 
        match turl.url_port with
        | Some(p) -> p
        | None -> failwith "request with response should always have a port"
      in
      

      let filename  = Printf.sprintf "%s.%s.%s.%d.%s"
        mthd 
        ( Types.Protocol.show url.url_protocol )
        ( Types.Domain.show domain )
        ( port )
        ( 
          match url.url_path with
          | Coq_url_path_blob (_, _) -> "blob"
          | _ -> Types.URLPath.show url.url_path
        )

      in 

      (* generate the html/image data (I believe this can be anything, but I can always have a valid iamge )*)

      let st = if st.csp_check && (st.csp_check_response = nonce ) then (
        Cspcheck.CSPChecker.generate_assertions st
      ) else st 
      in

      let bdy = 
        match content with 
        | Some (ContentElementImage (url)) -> ( Types.URL.show (States.VerifierState.translate_url st url) )
        | Some (ContentElementScript (script)) -> ( 
          let path = States.VerifierState.find_script_by_src st script.script_src in 
          let path = 
            match path with 
            | Some(p) -> p
            | None -> failwith "Script not recognized" 
          in 
          let sc = Types.NestedDOMPath.Map.find path st.scripts in 
          sc.repr
          )
        | Some (ContentElementFrame (_frame, html)) -> ( 
          if st.csp_check && (st.csp_check_response = nonce ) then (
              Html.Translator.html_to_string st html (Some(st.csp_check_urls))
          )
          else (
            Html.Translator.html_to_string st html None
          )
        )
        | Some (ContentElementHTML (html)) -> ( 
          if st.csp_check && (st.csp_check_response = nonce ) then (
              Html.Translator.html_to_string st html (Some(st.csp_check_urls))
            )
            else (
              Html.Translator.html_to_string st html None
          )
          )
        | _ -> ""
      in

      (* add the code to the headers *)
      let r_headers = `Assoc [ ("code", `String code) ; ("headers", Types.ResponseHeaders.to_yojson headers)] in

      let r_headers = 
        if st.csp_check then (
          match headers.rp_hd_csp with
          | None -> add_report_uri r_headers true
          | Some(csp_hd) ->
            add_report_uri r_headers false 
        ) else ( r_headers)
      in

      let output_headers = Yojson.Safe.pretty_to_string r_headers in 

      (* crete an assert for the request *)
      let uuid = Uuid.Generator.gen_uuid () in 
      let st = States.VerifierState.assert_add st uuid filename false in

      let req_ver = uuid in
    
      Utils.write_to_file ("output/" ^ filename ^ ".ver") req_ver ;
      Utils.write_to_file ("output/" ^ filename ^ ".headers") output_headers ;
      Utils.write_to_file ("output/" ^ filename ^ ".body") bdy ;

      st
    )

  let domupdate_handler (st : t) (path : Types.NestedDOMPath.t) : t = 
    st


  let evscriptupdatehtml_handler (st : t) (src : Types.NestedDOMPath.t) (trgt : Types.NestedDOMPath.t) (w : Types.Window.t) : t = 
    st


  let handle (st : t)  ( p : (Types.Event.t * Types.State.t option)) : t = 
    let (ev, state) = p in 
    match ev with
    | EvInit -> ( print_endline "EvInit" ; st )
    | EvRequest (em, req, nonce) -> (print_endline "EvRequest" ; request_handler st em req nonce state)
    | EvResponse (resp, nonce) -> (print_endline "EvResponse" ; response_handler st resp nonce  )
    | EvDOMUpdate path -> ( print_endline "EvDOMUpdate resp" ; domupdate_handler st path ) 
    | EvScriptUpdateHTML (src,trgt, w) ->( print_endline "EvScriptUpdateHTML"; evscriptupdatehtml_handler st src trgt w)
    | EvScriptDomainRelaxation (_, _) ->( print_endline "EvScrptDomainRelaxation" ; st ) 
    | EvWorkerCacheMatch _ -> ( print_endline "EvWorkerCacheMatch" ; st ) 
    | EvWorkerUpdateCache (_, _) ->( print_endline "EvWorkerUpdateCache" ; st ) 
    | EvScriptUpdateCache (_, _, _) ->( print_endline "EvScriptUdateCache" ; st ) 
    | EvScriptSetCookie (_, _, _, _) ->( print_endline "EvScriptSetCookie" ; st ) 
    | EvScriptNavigateFrame (_, _, _, _) ->( print_endline "EvScriptNavigateFrame" ; st ) 
    | EvScriptPostMessage (_, _, _) ->( print_endline "EvScriptPostMessage" ; st ) 
    | EvScriptCreateBlobUrl (_, _) ->( print_endline "EvScriptCreateBlobUrl" ; st ) 
    | EvScriptStorageSetItem (_, _, _, _) ->( print_endline "EvScriptStorageSetItem" ; st )
end

