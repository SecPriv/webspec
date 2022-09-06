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



type assertion_t = {
  order : int;
  lock : string;
  uuid : string ;
  value : string ;
}

type sw_t = {
  origin : Types.Origin.t ; 
  cache : string ; 
  events : (Types.Event.t * Types.State.t * int) list
}

type blob_t = {
	current : int ; (* current index of the blob uuids *)
	uuids : string list ; (* list of uuids for communicating the blob url value *)
	idx : int ; (* blob store index *)
}

type action_t = {
  repr : string;
  assertion : int;
  blob : Types.URL.t option;
}

type script_t = {
  url : Types.URL.t;
  events : (Types.Event.t * Types.State.t * int) list;
  repr : string
} [@@deriving show, eq, ord, yojson]

module type S =
sig
  type t
  val empty : t

  (* RoundTrip-related functions*)
  val add_request : t -> Types.Event.t -> t
  val add_response : t -> Types.Event.t -> t
  val find_response : t -> Types.Int.t -> Types.Response.t 
  val find_response_opt : t -> Types.Int.t -> Types.Response.t option 
  val find_response_r : t -> Types.Response.t -> Types.Int.t option
  val find_request : t -> Types.Int.t -> Types.Request.t 
  val find_request_opt : t -> Types.Int.t -> Types.Request.t option 
  val find_request_r : t -> Types.Request.t -> Types.Int.t option 

  (* Script-related functions*)
  val script_add : t -> Types.NestedDOMPath.t -> Types.Int.t -> t
  val script_update : t -> Types.NestedDOMPath.t -> Types.Event.t -> Types.State.t -> int -> t
  val script_update_repr : t -> Types.NestedDOMPath.t -> string -> t
  val script_targets : t -> Types.NestedDOMPath.t list 
  val script_sources : t -> Types.NestedDOMPath.t list 
  val find_script_by_src : t -> Types.URL.t -> Types.NestedDOMPath.t option

  (* DOM-related functions*)
  val dom_create :  
    t -> Types.NestedDOMPath.t -> Types.Int.t -> t

  val dom_update : 
    t -> Types.NestedDOMPath.t -> Types.Int.t -> t


  val update_ports : t -> Model.Browser.coq_Protocol -> int -> t
  val update_domains :  t -> Model.Browser.coq_Domain -> t
  val update_origins :  t -> Model.Browser.coq_Origin -> t
  val update_urls :  t -> Types.URL.t -> t
  val update_url_sources :  t -> Types.URL.t -> Types.HTMLElement.t option -> t
  val translate_port : t -> Types.Int.t -> Types.Int.t
  val translate_url : t -> Types.URL.t -> Types.URL.t
  val translate_origin : t -> Types.Origin.t -> Types.Origin.t
  val translate_response_headers : t -> Types.ResponseHeaders.t -> Types.ResponseHeaders.t
  val translate_request_headers : t -> Types.RequestHeaders.t -> Types.RequestHeaders.t

  val service_worker_add : t -> Types.Origin.t -> string -> t
  val service_worker_update : t -> Types.Origin.t -> Types.Event.t -> Types.State.t -> int -> t

  val assert_add : t -> string -> string -> bool -> t
  val assert_change : t -> int -> string -> bool -> t
  val action_add : t -> string -> int -> Types.URL.t option -> t
  val get_next_uuid : t -> assertion_t -> string option 
  val get_wait_uuid : t -> assertion_t -> string option 

  val blobstore_get_index : t -> Types.URL.t -> int 
  val blobstore_get_blob : t -> Types.URL.t -> Types.State.t option -> Types.Blob.t
  val blob_get : t -> Types.URL.t -> int -> blob_t
  val blob_add : t -> Types.URL.t -> int -> t
  val blob_uuid_add : t -> Types.URL.t -> int -> t
  val blob_current_uuid : t -> Types.URL.t -> int -> string
  val blob_next_uuid :  t -> Types.URL.t -> int -> t

  val get_window_from_dompath : t -> Types.NestedDOMPath.t -> Types.Window.t -> Types.Window.t
  val set_csp_check : t -> Types.CSP.t option -> int -> Types.URL.t -> t 
end


type verifier_state = {
  request: Types.Event.t Types.Int.Map.t; 
  response: Types.Event.t Types.Int.Map.t; 
  correlators : Types.Int.t list;
  scripts : script_t Types.NestedDOMPath.Map.t ; 
  port_remap : Types.Int.t Types.Int.Map.t;
  proto_ports : Types.Int.Set.t Types.Protocol.Map.t;
  domains :  Types.Int.Set.t Types.Int.Map.t;
  origins :  Types.Origin.Set.t;
  urls : Types.URL.Set.t;
  url_sources : Types.HTMLElement.t option Types.URL.Map.t;
  trace : Trace.t option ;
  asserts_ordered : assertion_t list ;
  asserts : assertion_t list ;
  actions : action_t list;
  sws : sw_t list;
  blobs : (int * blob_t) list Types.URL.Map.t ;
  csp : Types.CSP.t option ;
  csp_context_url : Types.URL.t option ; 
  csp_check_response : int ;
  csp_check_urls : string list ; 
  creator_blob : Types.URL.t option ;
  csp_check : bool ;
}

let stash_utils = "let STASH_RESPONDER = \"wss://web-platform.test:8666/stash_responder_blocking\";\n
class StashUtils {
  static putValue(key, value) {
    return new Promise(resolve => {
        const ws = new WebSocket(STASH_RESPONDER);
        ws.onopen = () => {
          ws.send(JSON.stringify({action: 'set', key: key, value: value}));
        };
        ws.onmessage = e => {
          ws.close();
          resolve();
        };
    });
  }

  static takeValue(key) {
    return new Promise(resolve => {
      const ws = new WebSocket(STASH_RESPONDER);
      ws.onopen = () => {
        ws.send(JSON.stringify({action: 'get', key: key}));
      };
      ws.onmessage = e => {
        ws.close();
        resolve(JSON.parse(e.data).value);
      };
    });
  }
}
"

module VerifierState : S with type t = verifier_state = 
struct
  type t = verifier_state

  let initialize_domains : Types.Int.Set.t Types.Int.Map.t = 
    let sbd = (Types.Int.Set.add 13377 Types.Int.Set.empty) in
    Types.Int.Map.add 13377 sbd Types.Int.Map.empty

  let empty = {
    request = Types.Int.Map.empty ; 
    response = Types.Int.Map.empty ;
    correlators = [];
    scripts = Types.NestedDOMPath.Map.empty ;
    port_remap = Types.Int.Map.empty;
    proto_ports = List.fold_left (fun acc p -> Types.Protocol.Map.add p Types.Int.Set.empty acc) 
      Types.Protocol.Map.empty [Model.Browser.ProtocolHTTP ; Model.Browser.ProtocolHTTPS ; Model.Browser.ProtocolData ; Model.Browser.ProtocolBlob] ;
    domains = initialize_domains ;
    origins = Types.Origin.Set.empty;
    urls =Types.URL.Set.empty;
    url_sources = Types.URL.Map.empty;
    trace = None ;
    asserts_ordered = [] ; 
    asserts = [] ; 
    actions = [] ;
    sws = [] ;
    blobs = Types.URL.Map.empty ;
    csp = None ;
    csp_context_url = None ; 
    csp_check_response = (-1) ; 
    csp_check_urls = [] ;
    creator_blob = None ;
    csp_check = false;
  }

  let add_request (st : t) (req : Types.Event.t) : t  = 
    match req with
    | EvRequest (_em, _r, corr) -> (
      let st = { st with correlators=(corr :: st.correlators)} in
      let request = Types.Int.Map.add corr req st.request in { st with request }
    )
    | _ -> st

  let add_response (st : t) (res : Types.Event.t) : t  = 
    (* the correlator should already be in the map*)
    match res with
    | EvResponse (_r, corr) -> let response = Types.Int.Map.add corr res st.response in { st with response }
    | _ -> st

  let find_response (st : t) (correlator : Types.Int.t) : Types.Response.t = 
    let ev_resp = Types.Int.Map.find_opt correlator st.response in

    match (ev_resp : Types.Event.t option) with
    | Some(EvResponse (resp, _)) -> resp
    | _ -> failwith "response is not registered in the verifier's state"

  let find_response_opt (st : t) (correlator : Types.Int.t) : Types.Response.t option = 
    let ev_resp = Types.Int.Map.find_opt correlator st.response in

    match (ev_resp : Types.Event.t option) with
    | Some(EvResponse (resp, _)) -> Some(resp)
    | _ -> None

  let find_response_r (st : t) (resp : Types.Response.t) :  Types.Int.t option = 
    let matches = Types.Int.Map.filter (fun k _ -> Types.Response.equal (find_response st k) resp) st.response in 

    (* sort descending *)
    let sorted_pairs = List.sort (fun (k1, _v1) (k2, _v2) -> k1 - k2) (Types.Int.Map.bindings matches) in

    match sorted_pairs with
    | [] -> None
    | (corr, _) :: _ -> Some(corr)


  let find_request (st : t) (correlator : Types.Int.t) : Types.Request.t = 
    let ev_req = Types.Int.Map.find_opt correlator st.request in

    match (ev_req : Types.Event.t option) with
    | Some(EvRequest (_, req, _)) -> req
    | _ -> failwith "request not registered in verifier's state"

  let find_request_opt (st : t) (correlator : Types.Int.t) : Types.Request.t option = 
    let ev_req = Types.Int.Map.find_opt correlator st.request in

    match (ev_req : Types.Event.t option) with
    | Some(EvRequest (_, req, _)) -> Some(req)
    | _ -> None

  let find_request_r (st : t) (req : Types.Request.t) :  Types.Int.t option = 
    let matches = Types.Int.Map.filter (fun k _ -> Types.Request.equal (find_request st k) req) st.request in 

    (* sort descending *)
    let sorted_pairs = List.sort (fun (k1, _v1) (k2, _v2) -> k1 - k2) (Types.Int.Map.bindings matches) in

    match sorted_pairs with
    | [] -> None
    | (corr, _res) :: _ -> Some(corr)

  let script_add (st : t) (path : Types.NestedDOMPath.t) (correlator : Types.Int.t) : t =
    (* let verify_func = "let STASH_RESPONDER = \"wss://web-platform.test:8666/stash_responder_blocking\";\nasync function stash_write(uuid, data, stash_responder){\n\tconst ws = new WebSocket(stash_responder);\n\tws.onopen = () => {\n\t\tws.send(JSON.stringify({action: 'set', key: uuid, value: data}));\n\t};\n}\n" in *)
    Option.value ~default:st (
      Option.bind (find_response_opt st correlator)
        (fun r -> Some({st with scripts=(Types.NestedDOMPath.Map.add path {url=r.rp_url ; events=[]; repr=stash_utils} st.scripts)}))
    )

  let script_update (st : t) (path : Types.NestedDOMPath.t) (ev : Types.Event.t) (tst : Types.State.t) (asser : int): t = 

    let scr = Types.NestedDOMPath.Map.find_opt path st.scripts in
    match scr with 
      | None -> st
      | Some(s) -> (
        let events = s.events in 
        let scr = { s with events = (events @ [(ev, tst, asser)])} in
        {st with scripts=(Types.NestedDOMPath.Map.add path scr st.scripts)}
      )

  let script_update_repr (st : t) (path : Types.NestedDOMPath.t) (l : string) : t = 

    let scr = Types.NestedDOMPath.Map.find_opt path st.scripts in
    match scr with 
      | None -> st
      | Some(s) -> (
        let repr = s.repr in 
        let scr = { s with repr = (repr ^ l ^ "\n")} in
        {st with scripts=(Types.NestedDOMPath.Map.add path scr st.scripts)}
      )


  let script_targets (st : t) : Types.NestedDOMPath.t list =
    let scripts : script_t list = List.map (fun bindings -> let _, scr = bindings in scr) (Types.NestedDOMPath.Map.bindings st.scripts) in
 
    let scripts_with_events = List.filter (fun (x : script_t) -> match x.events with [] -> false | _ -> true) scripts in

    let events = List.fold_left (fun acc sc -> List.append sc.events acc) [] scripts_with_events in 

    List.filter_map (fun ((ev, _tst, _asser) : (Types.Event.t * Types.State.t * int)) -> 
          match ev with 
          | EvScriptUpdateHTML (_, target, _) -> Some(target )
          | EvScriptSetCookie (_, target, _, _) -> Some(target)
          | EvScriptNavigateFrame (_, target, _, _) -> Some(target)
          | EvScriptPostMessage (_, target, _) -> Some(target)
          | _ -> None
      ) events

  let script_sources (st : t) :Types.NestedDOMPath.t list =
    List.map (fun bindings -> let key, _ = bindings in key) (Types.NestedDOMPath.Map.bindings st.scripts) 


  let find_script_by_src (st : t) (url : Types.URL.t) : Types.NestedDOMPath.t option = 
    let entries = Types.NestedDOMPath.Map.bindings st.scripts in

    let matches = List.filter (fun (_k, v) -> Types.URL.equal url v.url) entries in

    match matches with 
    | [] -> None
    | (path, _scrpt) :: _ -> Some(path)


  let dom_create (st : t) (_path : Types.NestedDOMPath.t) (_corr : Types.Int.t) : t = 
    st

  let dom_update (st : t) (_path : Types.NestedDOMPath.t) (_corr : Types.Int.t) : t = 
    st

  let rec _generate_new_port (st : t) (port : int) : int =
    if Types.Int.Map.mem port st.port_remap || port < 1024 then
      (* generate a new one*)
      let new_port = 1024 + (Types.Int.Map.cardinal st.port_remap)
      in
      ( assert (new_port <= 65535) ; _generate_new_port st new_port )
    else 
      port 
  

  let update_ports (st : t) (proto : Types.Protocol.t) (port : int) : t =
    (* remap  the port to a valid one *)
    if Types.Int.Map.mem port st.port_remap then
      st
    else 
      let new_port = _generate_new_port st port in
      let port_remap = Types.Int.Map.add port new_port st.port_remap in

      let current_ports_for_proto = Types.Protocol.Map.find proto st.proto_ports in
      
      let proto_ports = Types.Protocol.Map.add proto (Types.Int.Set.add new_port current_ports_for_proto) st.proto_ports in

      { st with port_remap ; proto_ports }


  let update_domains (st : t) (host : Types.Domain.t) : t = 

    let domains : Types.Int.Set.t Types.Int.Map.t = 
      ( match host with
        | Coq_domain (dmn) -> (
            let subdomains = try Types.Int.Map.find dmn st.domains with
                Not_found -> Types.Int.Set.empty
            in
            Types.Int.Map.add dmn subdomains st.domains
          )
        | Coq_subdomain (sbdmn, dmn) -> (
            let subdomains = try Types.Int.Map.find dmn st.domains with
                Not_found -> (* if it is not there, return an empty set to add the subdomain to *)
                Types.Int.Set.empty
            in

            (* update the set with the subdomain *)
            let updated_subdomains = Types.Int.Set.add sbdmn subdomains in

            (* add it to the map (whether it is an empty set)*)
            Types.Int.Map.add dmn updated_subdomains st.domains
          )
      ) in
    {st with domains }

  let update_origins (st : t) (origin : Types.Origin.t) : t = 
    let origins = Types.Origin.Set.add origin st.origins in

    {st with origins}


  let update_urls (st : t) (url : Types.URL.t) : t = 
    let urls = Types.URL.Set.add url st.urls in

    {st with urls}


  let update_url_sources (st : t) (url : Types.URL.t) (src : Types.HTMLElement.t option): t = 
    let url_sources = Types.URL.Map.add url src st.url_sources in

    {st with url_sources}

  let translate_port (st : t) (port : Types.Int.t) : Types.Int.t = 
      Option.value ~default:port (Types.Int.Map.find_opt port st.port_remap) 
  
  let translate_url (st : t) (url : Types.URL.t) : Types.URL.t = 
    (* translate ports *)
    (* maybe also translate the origin *)
    match url.url_port with
    | Some (v) -> 
      { url with url_port = Some(translate_port st v) }
    | _ -> { url with url_port = Some(Utils.port_from_protocol url.url_protocol)}


  let translate_origin (st : t) (origin : Types.Origin.t) : Types.Origin.t = 
    (* nothing to do so far -> when I implement origin remapping (likely never), translate it here*)
    match origin with
    | TupleOrigin (proto, dom_opt, port_opt) -> (
      match port_opt with
      | Some (v) -> TupleOrigin (proto, dom_opt, Some(translate_port st v))
      | _ -> TupleOrigin (proto, dom_opt, Some(Utils.port_from_protocol proto))
    )
    | _ -> origin 

  let translate_response_headers (st : t) (headers : Types.ResponseHeaders.t) : Types.ResponseHeaders.t =

    let hd_csp : Types.CSP.t option = headers.rp_hd_csp in

    let csp_script_src : Types.CSPSrc.t option = 
      match hd_csp with 
      | Some(csp) -> (
        match (csp.csp_script_src : Types.CSPSrc.t option) with
        | Some(CSPSrcSource (proto, subd, dom, port, path)) ->
          (
            let port = 
              match port with 
              | None -> None
              | Some(p) -> Some(translate_port st p)
            in
            Some(CSPSrcSource (proto, subd, dom, port, path))
          )
        | Some(x) -> Some(x)
        | _ -> None
        )
      | None -> None
      in
      
    
    let headers = match csp_script_src with 
    | None -> headers
    | Some(csc) -> (
      match (headers.rp_hd_csp : Types.CSP.t option) with
      | None -> headers
      | Some (csp) -> { headers with rp_hd_csp=(Some({ csp with csp_script_src=(Some(csc))}))}
    ) 
    in

    let headers = 
      match headers.rp_hd_access_control_allow_origin with
      | None -> headers
      | Some(origin) -> {headers with rp_hd_access_control_allow_origin=(Some(translate_origin st origin))}

    in 
    
    match headers.rp_hd_location with
    | None -> headers
    | Some(url) -> {headers with rp_hd_location=(Some(translate_url st url))}

  let translate_request_headers (st : t) (headers : Types.RequestHeaders.t) : Types.RequestHeaders.t =
    let rq_hd_origin = Option.bind headers.rq_hd_origin (fun orig -> Some(translate_origin st orig)) in

    let rq_hd_referer = Option.bind headers.rq_hd_referer (fun url -> Some(translate_url st url)) in

    { headers with rq_hd_origin ; rq_hd_referer }

  let service_worker_add (st : t) (og : Types.Origin.t) (cache : string) : t = 
    let sws = {origin=og; cache=cache; events=[]} :: st.sws in
    { st with sws }

  let service_worker_update (st :t) (og : Types.Origin.t) (ev : Types.Event.t) (tst : Types.State.t) (ass : int) : t = 
    let sw = try List.find (fun s -> s.origin = og) st.sws with 
      Not_found -> ({origin=og ; cache=(Utils.rand_str 10) ; events=[]}) 
    in

    let events = sw.events @ [(ev , tst , ass)] in

    let sws = List.map (fun s -> if s.origin = og then {s with events} else s) (sw :: st.sws) in
    
    { st with sws }

  let assert_change (st : t) (idx : int) (vv : string) (ordered: bool) : t =
    if ordered then (
      let asserts_ordered = List.map (fun el -> if el.order = idx then ({el with value=vv ;}) else el) st.asserts_ordered
      in
      { st with asserts_ordered }
    ) else (
        let asserts = List.map (fun el -> if el.order = idx then ({el with value=vv ;}) else el) st.asserts
        in
      { st with asserts }
    )

  let assert_add (st : t) (key : string) (vv : string) (ordered: bool): t = 
    if ordered then (
      let l = List.length st.asserts_ordered in
      let lock_uuid = Uuid.Generator.gen_uuid () in 
      (* let st = uuid_next st in *)
      let asserts_ordered = st.asserts_ordered @ [ {order=l ; lock=lock_uuid; uuid=key ; value=vv} ] in 
      { st with asserts_ordered }

    )
    else (
      let asserts = st.asserts @ [ {order=(-1) ; lock=""; uuid=key ; value=vv } ] in 
      { st with asserts }
    )

  let action_add (st : t) (rep : string) (ass_idx : int) (url:Types.URL.t option): t = 
    let actions = st.actions @ [ {repr=rep; assertion=ass_idx; blob=url} ] in 
    { st with actions }
    
  let get_next_uuid (st : t) (ass : assertion_t) : string option = 
    let len = List.length st.asserts_ordered in 
    let next = (ass.order + 1) in
    if len == next then (
      None
    ) else (
      let next_assert = List.nth st.asserts_ordered next in 
      Some(next_assert.lock)
    )

  let get_wait_uuid (st : t) (ass : assertion_t) : string option = 
    if ass.order == 0 then (
      None
    ) else (
      Some(ass.lock)
    )

  let blobstore_get_index (st : t) (url : Types.URL.t) : int =
    match url.url_protocol, url.url_path with 
    | ProtocolBlob, Coq_url_path_blob(_, i) -> i
    | _ -> failwith "[blobstore_get_blob] Malformed blob url"

  let blobstore_get_blob (st : t) (url : Types.URL.t) (tst : Types.State.t option): Types.Blob.t =
    let ttst = try Option.get tst with
      Invalid_argument _ -> failwith ("[VerifierState blobstore_get_blob] No state: " ^ (Types.URL.show url))
    in

    let idx = 
      match url.url_protocol, url.url_path with 
      | ProtocolBlob, Coq_url_path_blob(_, i) -> i
      | _ -> failwith "[blobstore_get_blob] Malformed blob url"
    in

    Option.get @@ Model.Array.select ttst.st_blob_store idx


    

  let blob_get (st : t) (url : Types.URL.t) (idx : int) : blob_t = 
    let blobs = try Types.URL.Map.find url st.blobs with 
      Not_found -> failwith "Blob not found in verifier state"
    in

    List.assoc idx blobs

  let blob_add (st : t) (url : Types.URL.t) (idx : int): t = 
    let blobs_row = Option.value ~default:[] (Types.URL.Map.find_opt url st.blobs) in

    let blobs_row = (idx, {current=0;uuids=[];idx=0}) :: blobs_row in

    let blobs = Types.URL.Map.add url blobs_row st.blobs in

    { st with blobs }


  let blob_uuid_add (st : t) (url : Types.URL.t) (idx : int): t =
    let st = 
      match Types.URL.Map.mem url st.blobs with
      | true -> st 
      | false -> blob_add st url idx
    in
    let blob = blob_get st url idx in
    let uuid = Uuid.Generator.gen_uuid () in 
    let uuids = uuid :: blob.uuids in

    let blob_row = (idx, {blob with uuids}) :: (Types.URL.Map.find url st.blobs) in

    let blobs = Types.URL.Map.add url blob_row st.blobs in
    { st with blobs}

  let blob_current_uuid (st : t) (url : Types.URL.t) (idx : int): string =
    let blob = blob_get st url idx in
    try List.nth blob.uuids blob.current with
      Not_found -> failwith "uuid index out of bounds"
  
  let blob_next_uuid (st : t) (url : Types.URL.t) (idx : int) : t = 
    let blob = blob_get st url idx in
    let blob = { blob with idx=(blob.idx+1)} in
    let blob_array = (idx, blob) :: (Types.URL.Map.find url st.blobs) in 


    let blobs = Types.URL.Map.add url blob_array st.blobs in
    { st with blobs}

  let rec get_window_from_dompath  (st : t) (path : Types.NestedDOMPath.t) (st_window : Types.Window.t) : Types.Window.t = 
    let trace = Option.get st.trace in

    match path with 
    | DOMPath ([], selector) -> (
      match selector with 
      | DOMTopLevel -> st_window
      | DOMIndex i -> (
        let del = Model.Array.select st_window.wd_document.dc_dom.dm_body i in
        match del with 
        | Some(DOMElementResource (_, (ContentElementFrame (frm, _)))) -> (
          Model.Array.select trace.global.windows frm.frame_window
        )
        |  _ -> failwith "[get_window_from_dompath] nested dom path does not point to a frame"
      )
    )
    | DOMPath (hd :: tl, selector) -> (
        let del = Model.Array.select st_window.wd_document.dc_dom.dm_body hd in
        match del with 
        | Some(DOMElementResource (_, (ContentElementFrame (frm, _)))) -> (
          let new_window = Model.Array.select trace.global.windows frm.frame_window in
          get_window_from_dompath st (DOMPath (tl, selector)) new_window
        )
        |  _ -> failwith "[get_window_from_dompath] nested dom path does not go through frames"

    )

  let set_csp_check (st : t) (t_csp : Types.CSP.t option) (rp_idx : int) (u : Types.URL.t): t =
    { st with csp=t_csp ; csp_check=true ; csp_check_response=rp_idx ; csp_context_url=(Some(u)) }

end

