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
  type t 

  val empty : t
  val to_yojson : t -> Yojson.Safe.t
  val state_to_config : States.VerifierState.t -> t 

end

type config = {
  ports : Types.Int.Set.t Types.Protocol.Map.t ;
  browser_host : Types.Domain.t;
  alternate_hosts : Types.Int.Set.t; 
  subdomains : Types.Int.Set.t
}

module Config : S with type t = config =
struct
  type t = config 

  let empty : t = {
    ports = Types.Protocol.Map.empty ;
    browser_host = Coq_domain (-1) ;
    alternate_hosts = Types.Int.Set.empty ;
    subdomains = Types.Int.Set.empty
  }

  let default_ports = (* blob and data are not really needed *) 
    Types.Protocol.Map.of_seq (List.to_seq [(Model.Browser.ProtocolHTTP, Types.Int.Set.add 8080 Types.Int.Set.empty) 
    ; (Model.Browser.ProtocolHTTPS , Types.Int.Set.add 8443 Types.Int.Set.empty) 
    ; (Model.Browser.ProtocolBlob , Types.Int.Set.add 8080 Types.Int.Set.empty) 
    ; (Model.Browser.ProtocolData , Types.Int.Set.add 8080 Types.Int.Set.empty) ])

  let ports_to_yojson (ports : Types.Int.Set.t Types.Protocol.Map.t) : Yojson.Safe.t =
    `Assoc [ 
      ("http", `List (List.fold_left (fun acc x -> `Int x :: acc ) [`Int 8000] (Types.Int.Set.elements (Types.Protocol.Map.find Model.Browser.ProtocolHTTP ports))) ) ;
      ("https", `List (List.fold_left (fun acc x -> `Int x :: acc ) [`Int 8444 ; `Int 8445] (Types.Int.Set.elements (Types.Protocol.Map.find Model.Browser.ProtocolHTTPS ports))) ) ;
      ("ws", `List [`Int 8665] ) ;
      ("wss", `List [`Int 8666] ) ;
      ("http-public", `List [`String "auto"] ) ;
      ("http-private", `List [`String "auto"] ) ;
      ("https-public", `List [`String "auto"] ) ;
      ("https-private", `List [`String "auto"] ) ;
    ]


  let hosts_to_yojson (hosts : Types.Int.Set.t)  : Yojson.Safe.t =
    (* generate key name and add hosts as a k,v pair *)
    let init = [("alt:", `String "not-web-platform.test")] in
    let hosts_list =  ( List.fold_left (fun acc x -> ((Printf.sprintf "alt%d" x), `String (Printf.sprintf "%d.test" x)) :: acc) init (Types.Int.Set.elements hosts) ) in
    `Assoc ( hosts_list )

  let calculate_hosts_product (hosts : Types.Int.Set.t) (subdomains : Types.Int.Set.t) : Types.String.t list = 
    List.fold_left (fun acc_out host -> List.append (List.fold_left (fun acc_in sbd -> (Printf.sprintf ("%d.%d") sbd host) :: acc_in) [] (Types.Int.Set.elements subdomains)) acc_out ) 
      [] (Types.Int.Set.elements hosts)
  
  let subdomains_to_yojson (subdomains : Types.Int.Set.t) : Yojson.Safe.t =
    `List (List.fold_left (fun acc_in sbd -> (`String (string_of_int sbd)) :: acc_in) [] (Types.Int.Set.elements subdomains))
   
  let to_yojson (ist : t) : Yojson.Safe.t = 
    `Assoc [ 
      ("browser_host", `String "web-platform.test") ;
      ("alternate_hosts", hosts_to_yojson ist.alternate_hosts) ;
      ("ports", ports_to_yojson ist.ports ) ;
      ("subdomains", subdomains_to_yojson ist.subdomains) ; 
      ("ssl", Yojson.Safe.from_string "
        {
            \"type\": \"pregenerated\",
            \"encrypt_after_connect\": false,
            \"openssl\": {
                \"openssl_binary\": \"openssl\",
                \"base_path\": \"tools/certs\",
                \"password\": \"web-platform-tests\",
                \"force_regenerate\": false,
                \"duration\": 30,
                \"base_conf_path\": \"/usr/lib/ssl/openssl.cnf\"
            },
            \"pregenerated\": {
                \"host_key_path\":  \"tools/certs/web-platform.test.key\",
                \"host_cert_path\": \"tools/certs/web-platform.test.pem\" 
            },
            \"none\": {}
        }") ;
      ("aliases", `List []) ;
      ("check_subdomains", `Bool true) ;
      ("log_level", `String "debug") ; 
      ("bind_address", `Bool true) ; 
    ]

  let merge_ports (st : t) (entry : Types.Protocol.t * Types.Int.Set.t) : t =
    let (proto, ports) = entry in
    let current_ports : Types.Int.Set.t = Option.value ~default:Types.Int.Set.empty (Types.Protocol.Map.find_opt proto st.ports)  in
    let current_ports = Types.Int.Set.union ports current_ports in

    let ports =
      match proto with
        | ProtocolHTTP -> Types.Protocol.Map.add ProtocolHTTP current_ports st.ports
        | ProtocolHTTPS -> Types.Protocol.Map.add ProtocolHTTPS current_ports st.ports
        | ProtocolBlob -> Types.Protocol.Map.add ProtocolBlob current_ports st.ports
        | ProtocolData -> Types.Protocol.Map.add ProtocolData current_ports st.ports

    in
    { st with ports }

  let get_domain (domain : Types.Domain.t option) : int = 
    match domain with
    | Some(Coq_domain (d)) -> d
    | Some(Coq_subdomain (d, sd)) -> d
    | None -> -1

  let get_subdomain_opt (domain : Types.Domain.t option ) : int option = 
    match domain with
    | Some(Coq_subdomain (_, sd)) -> Some(sd)
    | _ -> None


  let state_to_config (st : States.VerifierState.t) : t = 
    (* 1. go through relevant urls *)
    (* 2. go through dummy urls *)
    (* 3. go through *)
    
    let state = { empty with ports=default_ports } in
    let state = List.fold_left merge_ports state (List.of_seq (Types.Protocol.Map.to_seq st.proto_ports)) in

    (* go through the urls and extract a list of domains *)

    (* go through relevant origins (proto, domain, port )*)

    (* make relevant origins alternate-host / maybe do this with lists*)

    let alternate_hosts = Types.Int.Map.fold (fun k v acc -> Types.Int.Set.add k acc) st.domains Types.Int.Set.empty in

    let subdomains = Types.Int.Map.fold (fun k v acc -> Types.Int.Set.union v acc) st.domains Types.Int.Set.empty  in

    let browser_host = Model.Browser.Coq_domain (-1) in

    { state with alternate_hosts ; subdomains ; browser_host }

end
