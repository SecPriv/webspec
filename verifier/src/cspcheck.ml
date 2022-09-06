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
  val generate_assertions : States.VerifierState.t -> States.VerifierState.t 
  val generate_checks : States.VerifierState.t -> States.VerifierState.t
end



module CSPChecker : S =
struct

  let show_url (st : States.VerifierState.t) (url : Types.URL.t) : string option = 
    let url = States.VerifierState.translate_url st url in

    match url with 
    | {url_protocol=ProtocolHTTP; url_host=_; url_port=_; url_path=(Coq_url_path_res (_))}
    | {url_protocol=ProtocolHTTPS; url_host=_; url_port=_; url_path=(Coq_url_path_res (_))} -> (
      Some(
        Printf.sprintf "%s://%s%s/%s" 
        (Types.Protocol.show url.url_protocol)
        (Option.value ~default:"" (Option.bind url.url_host (fun domain -> Some(Types.Domain.show domain))))
        (Option.value ~default:"" (Option.bind url.url_port (fun port -> Some(Printf.sprintf ":%d" port))))
        ("verifier/csp.py?order=")) 
      )
    | _ -> None

  let generate_url_variations (st : States.VerifierState.t) (proto : Types.Protocol.t option) (subd : int option option) (d : int option) (port : int option) : (string * string) list =
    let context_url = Option.get st.csp_context_url in
    let all_domains = Types.Int.Set.elements @@ Types.Int.Map.fold (fun k v acc -> Types.Int.Set.add k acc) st.domains Types.Int.Set.empty in
    let all_subdomains = Types.Int.Set.elements @@ Types.Int.Map.fold (fun k v acc -> Types.Int.Set.union v acc) st.domains Types.Int.Set.empty in
    let allowed_proto = Option.value ~default:context_url.url_protocol proto in
    print_endline "collecting subds" ;
    let allowed_subd = 
      match subd with 
      | None -> None 
      | Some(None) -> Some( List.hd all_subdomains ) 
      | Some(Some(d)) -> Some(d)
    in
    print_endline "collecting dmns" ;
    let allowed_dmn = Option.value ~default:(List.hd all_domains) d in
    let allowed_host : Types.Domain.t = 
      match allowed_subd, allowed_dmn with 
      | None, n -> Coq_domain(n)
      | Some(sn), n -> Coq_subdomain(sn, n)
    in
    let allowed_port = States.VerifierState.translate_port st @@ 
      Option.value ~default:(Utils.port_from_protocol allowed_proto) port 
    in

    let allowed_url : Types.URL.t = {
      url_protocol = allowed_proto; 
      url_host = Some(allowed_host);
      url_port = Some(allowed_port);
      url_path =  Coq_url_path_res(Coq_slash)
    } in

    let alt_proto : Types.Protocol.t = 
      match allowed_proto with 
      | ProtocolHTTP -> ProtocolHTTPS
      | ProtocolHTTPS -> ProtocolHTTP
      | _ -> failwith "[generate_url_variations] can only have http or https here"
    in
    print_endline "collecting alt subds" ;
    List.iter (fun x -> print_endline @@ string_of_int x) all_subdomains ;
    let alt_subd = 
      match allowed_subd with 
      | None -> List.hd all_subdomains
      | Some(sd) -> List.hd @@ List.filter (fun x -> x <> sd) all_subdomains 
    in
    print_endline "collecting alt dmns" ;
    let alt_dmn = List.hd @@ List.filter (fun x -> x <> allowed_dmn) all_domains in
    let alt_host1 : Types.Domain.t = Coq_subdomain(alt_subd, allowed_dmn) in
    let alt_host2 : Types.Domain.t = 
      match allowed_subd with
      | None -> Coq_domain(alt_dmn) 
      | Some(sd) -> Coq_subdomain(sd, alt_dmn)
    in
    print_endline "collecting alt ports" ;
    let alt_port = 
      List.hd @@ 
      List.filter (fun x -> x <> allowed_port) @@ 
      Types.Int.Set.elements  @@
      Types.Protocol.Map.find allowed_proto st.proto_ports
    in

    (* maybe some unnecessary stuff. clean up after*)
    let alt_port_proto = 
      try List.hd ( 
        Types.Int.Set.elements  @@
        Types.Protocol.Map.find alt_proto st.proto_ports
      ) with Failure _-> Utils.port_from_protocol alt_proto
     
    in

    (* Non-specified fields act as a wildcard and therefore should be allowed regardless of changing its value or not *)
    [
      ((Option.get @@ show_url st allowed_url) ^ (string_of_int 0), "G") ;
      ((Option.get @@ show_url st {allowed_url with url_protocol=alt_proto ; url_port=(Some(alt_port_proto))}) ^ (string_of_int 1), "P") ;
      ((Option.get @@ show_url st {allowed_url with url_host=(Some(alt_host1))}) ^ (string_of_int 2), match subd with | Some(Some(_)) | None -> "P" | Some(None) -> "G") ;
      ((Option.get @@ show_url st {allowed_url with url_host=(Some(alt_host2))}) ^ (string_of_int 3), match d with | Some(_) -> "P" | None -> "G") ;
      ((Option.get @@ show_url st {allowed_url with url_port=(Some(alt_port))}) ^ (string_of_int 4), match port with | Some(_) -> "P" | None -> "G") ;
    ] 



  let generate_assertions (st : States.VerifierState.t) : States.VerifierState.t = 
    (* add unordered assertions based on the CSP for checking. The CSP is registered in st *)
    let context_url = States.VerifierState.translate_url st @@ Option.get st.csp_context_url in
    let _blob = Option.get st.creator_blob in
    let csp = st.csp in

    let uuid = "b28a182a-b4c1-47ac-93a7-9667c56bf641" in

    (* 2. pattern match on the csp script-src *)
    let checklist = 
      match csp with 
      | None -> ( (* NO CSP *)
        (* hardcoded 5 that should pass *)
        [
          ("https://web-platform.test:8443/verifier/csp.py?order=0", "G") ;
          ("https://web-platform.test:8444/verifier/csp.py?order=1", "G") ;
          ("https://web-platform.test:8445/verifier/csp.py?order=2", "G") ;
          ("https://not-web-platform.test:8443/verifier/csp.py?order=3", "G") ;
          ("https://not-web-platform.test:8444/verifier/csp.py?order=4", "G") ;
        ] 
      )
      | Some(c) -> ( 
        match c.csp_script_src with 
        | Some(CSPSrcNone) -> (
          let backup_list =[
            "https://web-platform.test:8443" ;
            "https://web-platform.test:8444" ;
            "https://web-platform.test:8445" ;
            "https://not-web-platform.test:8443" ;
            "https://not-web-platform.test:8444" ;
          ] in
          let url_list = List.map Option.get @@ List.filter Option.is_some @@ List.fold_left (fun acc el -> (show_url st el) :: acc ) [] (Types.URL.Set.elements st.urls) in
          let url_list = List.filteri (fun i _ -> i < 5) url_list in
          let url_list = ( 
            if (List.length url_list) < 5 then (
              let diff = (5 - (List.length url_list )) in
              let to_add = List.filteri (fun i _ -> i < diff) backup_list in 
              url_list @ to_add 
            )
            else (
              url_list
            )
          ) in
          List.mapi (fun i el -> (el ^ (string_of_int i), "P")) url_list
        )
        | Some(CSPSrcSelf) -> (
            match context_url.url_host with 
            | Some(Coq_domain(d)) -> generate_url_variations st (Some(context_url.url_protocol)) None (Some(d)) context_url.url_port
            | Some(Coq_subdomain(sd, d)) -> generate_url_variations st (Some(context_url.url_protocol)) (Some(Some(sd))) (Some(d)) context_url.url_port
            | _ -> failwith "[generate_assertions] invalid context url"
          )
        | Some(CSPSrcScheme (proto)) -> generate_url_variations st (Some(proto)) None None None 
        | Some(CSPSrcSource (proto, subd, d, port, _)) -> generate_url_variations st proto subd (Some(d)) port
        | None -> ([
          ("https://web-platform.test:8443/verifier/csp.py?order=0", "G") ;
          ("https://web-platform.test:8444/verifier/csp.py?order=1", "G") ;
          ("https://web-platform.test:8445/verifier/csp.py?order=2", "G") ;
          ("https://not-web-platform.test:8443/verifier/csp.py?order=3", "G") ;
          ("https://not-web-platform.test:8444/verifier/csp.py?order=4", "G") 
        ])
    )
    in

    List.iter (fun (u, r) -> print_endline (Printf.sprintf "%s: %s" r u)) checklist ;

    let signature = List.fold_left (fun acc (u, v) -> acc ^ v) "" checklist in
    let checks = List.fold_left (fun acc (u, v) -> acc @ [u]) [] checklist in

    print_endline signature ;

    let st = { st with csp_check_urls=checks} in
    States.VerifierState.assert_add st uuid signature false 

  let generate_checks (st : States.VerifierState.t) : States.VerifierState.t = 
    (* get the csp to check *)
    let trace = Option.get st.trace in
    let _event = List.hd trace.events in
    let state = List.hd @@ List.rev trace.states in
    print_endline @@ Types.Event.show @@ List.hd trace.events ;
    print_endline @@ Types.State.show state ; 

    
    let context_window = 
        match List.hd trace.events with 
      | EvDOMUpdate (trgt) -> (
        States.VerifierState.get_window_from_dompath st trgt state.st_window
      )
      | _ -> failwith "Trace does not end with a DOMUpdate. Cannot check CSP"
    in

    let original_context_url = context_window.wd_location in
    let context_url : Types.URL.t = 
      match original_context_url with 
    | {url_protocol=ProtocolHTTP; url_host=_; url_port=_; url_path=_} 
    | {url_protocol=ProtocolHTTPS; url_host=_; url_port=_; url_path=_} 
    | {url_protocol=ProtocolData; url_host=_; url_port=_; url_path=_} -> original_context_url
    | {url_protocol=ProtocolBlob; url_host=_; url_port=_; url_path=(Coq_url_path_blob (og, _))} -> (
        match og with 
        | TupleOrigin (proto, dmn_opt, port_opt) -> (
          {url_protocol=proto; url_host=dmn_opt; url_port=port_opt; url_path=Coq_url_path_res(Coq_slash)} 
        )
        | _ -> failwith "[generate_checks] bloburl cannot have opaque origin"
    )
    | _ -> failwith "[generate_checks] invalid url"
    in
    let target_csp = context_window.wd_document.dc_headers.rp_hd_csp in

    print_endline @@ Types.CSP.show @@ Option.get target_csp ;
    print_endline @@ Types.Protocol.show context_url.url_protocol;
    print_endline @@ Types.URL.show @@ States.VerifierState.translate_url st original_context_url ;
    print_endline @@ Types.URL.show @@ States.VerifierState.translate_url st context_url ;

    let rp_idx = 
      match trace.events with
      | _hd :: (EvResponse (_, idx)) :: _tl -> idx
      | _ -> failwith "[generate_checks] EvResponse not found"
    in

    let resp = Types.Int.Map.find rp_idx st.response in
    (* this is bad. implement a VerifierState module function to update this field *)
    let st = 
      match resp with 
      | EvResponse (r, _) -> (
          match r.rp_url.url_protocol with 
          | ProtocolBlob -> { st with creator_blob=(Some(r.rp_url)) }
          | _ -> st
        )
      | _ -> failwith "[generate_checks] EvResponse not found"
    in

    (* add csp and response index to VerifierState *)
    let st = States.VerifierState.set_csp_check st target_csp rp_idx context_url in
    generate_assertions st 
    (* I think that's it? Then add a new function that creates the requests based on the CSP *)


end
