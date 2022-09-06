#require "sexplib";;

module Viz =
  struct

open Sexplib
open Printf

open Sexp

let cat_maybes lst = List.concat_map Option.to_list lst
let note_left n = sprintf "rnote left\n%s\nend note" n
let note_over e n = sprintf "rnote over %s\n%s\nend note" e n

let st_emitter = function
  | List (Atom "Build_State" :: Atom version :: event ::
            List (Atom "Build_FetchEngine" :: _ :: emitter :: _) :: _) -> emitter
  | _ -> failwith "Invalid State"

let response_code = function
  | List (Atom "Build_Response" :: url :: Atom code :: _) -> code
  | _ -> failwith "Invalid Response"

let emitter_from = function
  | List (Atom "EmitterCORSPreflight" :: _)
  | List (Atom "EmitterForm" :: _)
  | Atom "EmitterClient" -> "B"
  | List (Atom "EmitterScript" :: _) -> "JS"
  | Atom "EmitterWorker" -> "SW"
  | _ -> failwith "Invalid Emitter"

let (domain_to_domain_id, domain_legend) =
  let id = ref 0 in
  let map = ref [] in
  ((fun domain -> begin match List.assoc_opt domain !map with
                  | Some name -> name
                  | None -> incr id;
                            let name = sprintf "domain_%d" !id in
                            map := (domain, name) :: !map;
                            name
                  end)
  ,(fun () -> !map))

let (url_to_origin_id, origin_legend) =
  let id = ref 0 in
  let map = ref [] in
  let assoc_save (protocol, host, port) =
    match List.assoc_opt (protocol, host, port) !map with
    | Some name -> name
    | None -> incr id;
              let name = sprintf "origin_%d" !id in
              map := ((protocol, host, port), name) :: !map;
              name
  in
  let viz_origin = function
    | List (Atom b :: Atom protocol :: host :: port :: _)
         when b = "Build_URL" || b = "TupleOrigin" ->
       assoc_save (protocol, host, port)
    | List (Atom "OpaqueOrigin" :: Atom nonce :: _) ->
       assoc_save ("0", Atom nonce, Atom "0")
    | e -> failwith ("Invalid URL/Origin " ^ (to_string_hum e))
  in
  ((function
    | List (Atom "Build_URL" :: _ :: _ :: _ :: List (Atom "url_path_blob" :: origin :: _ ) :: _) ->
       viz_origin origin
    | List (Atom "Build_URL" :: _ :: _ :: _ :: List (Atom "url_path_data" :: nonce :: _ ) :: _) ->
       viz_origin (List [Atom "OpaqueOrigin"; nonce])
    | List (Atom b :: rest)
         when b = "Build_URL" || b = "TupleOrigin" || b = "OpaqueOrigin" ->
       viz_origin (List (Atom b :: rest))
    | e -> failwith ("Invalid URL/Origin " ^ (to_string_hum e)))
  ,(fun () -> !map))

let list_notation =
    let is_nil n = String.sub n 0 3 = "nil" in
    let is_cons c = String.sub c 0 4 = "cons" in
    function
    | Atom nil when is_nil nil -> "[]"
    | List ( Atom cons :: n :: Atom nil :: [] ) when is_cons cons && is_nil nil -> sprintf "[ %s ]" (to_string_hum n)
    | List lst -> (to_string_hum (List lst))
    | x -> failwith "Invalid List: " ^ (to_string_hum x)

let viz_emitter = function
  | List (Atom name :: List (Atom "DOMPath" :: lst :: path :: _) :: _) when name = "EmitterScript" -> sprintf "%s (DOMPath %s %s)" name (list_notation lst) (to_string_hum path)
  | List (Atom name :: idx :: _) when name = "EmitterScript" -> sprintf "%s %s" name (to_string_hum idx)
  | List (Atom name :: _) -> name
  | Atom name -> name
  | _ -> failwith "Invalid Emitter"

let viz_path = function
  | Atom "slash" -> "/"
  | List (Atom "anypath" :: Atom n :: _) -> "/" ^ n
  | _ -> failwith "Invalid Path"
       
let viz_url_path = function
  | List (Atom "url_path_data" :: nonce :: idx :: _ ) -> sprintf "[%s]%s" (to_string nonce) (to_string idx)
  | List (Atom "url_path_blob" :: origin :: idx :: _) -> sprintf "%s;%s" (url_to_origin_id origin) (to_string idx)
  | List (Atom "url_path_res" :: path :: _) -> viz_path path
  | _ -> failwith "Invalid URLPath"
       

let viz_cookie_name = function
  | List (Atom "NoPrefix" :: Atom name :: _) -> "c_" ^ name
  | List (Atom "Host" :: Atom name :: _) -> "__Host-c_" ^ name
  | List (Atom "Secure" :: Atom name :: _) -> "__Secure-c_" ^ name
  | x -> failwith "Not Implemented! "

let viz_url u = match u with
  | List (Atom "Build_URL" :: Atom protocol :: host :: port :: path :: _)
    when protocol = "ProtocolHTTP" || protocol = "ProtocolHTTPS" ->
     sprintf "%s%s" (url_to_origin_id u) (viz_url_path path)
  | List (Atom "Build_URL" :: Atom "ProtocolBlob" :: host :: port :: path :: _) ->
     sprintf "blob:%s" (viz_url_path path)
  | List (Atom "Build_URL" :: Atom "ProtocolData" :: host :: port :: path :: _) ->
     sprintf "data:%s" (viz_url_path path)     
  | e -> failwith ("Invalid URL " ^ (to_string e))

let viz_setcookie = function
  |  List (Atom "Build_SetCookie" :: name :: value :: domain
           :: reg_domain :: path :: secure :: httponly :: samesite :: _) ->
      sprintf "Set-Cookie: %s=%s%s%s%s%s%s"
                            (viz_cookie_name name) (Sexp.to_string_hum value)
                            (match domain with
                             | List (Atom "SomeDomain" :: domain :: _) ->
                                sprintf "; Domain=%s" (domain_to_domain_id domain)
                             | _ -> "")
                            (sprintf "; Path=%s" (viz_path path))
                            (match secure with | Atom "true" -> "; Secure" | _ -> "")
                            (match httponly with | Atom "true" -> "; HttpOnly" | _ -> "")
                            (sprintf "; SameSite=%s" (let n = (Sexp.to_string_hum samesite) in
                                                      (String.sub n 2  @@ (String.length n)-2)))
  | _ -> failwith "Invalid Set-Cookie"

let viz_rp_headers = function
  | List (Atom "Build_ResponseHeaders" ::
            ct :: cookie :: alloworigin :: location :: csp :: refpolicy :: _) ->
     [
       (match ct with
        | List (Atom "SomeContentType" :: Atom ct :: _) ->
           Option.some @@ "Content-Type: " ^ ct
        | _ -> None);
       (match alloworigin with
        | List (Atom "SomeOrigin" :: origin :: _) ->
           Option.some @@ "Access-Control-Allow-Origin: " ^ (url_to_origin_id origin)
        | _ -> None);
       (match location with
        | List (Atom "SomeURL" :: url :: _) ->
           Option.some @@ "Location: " ^ (viz_url url)
        | _ -> None);
       (match cookie with
        | List (Atom "SomeSetCookie" :: setcookie :: _ ) ->
           Option.some (viz_setcookie setcookie)
        | _ -> None);
       (match csp with
       | List (Atom "SomeCSP" :: List (Atom "Build_CSP" :: csp_script :: csp_tt :: _) :: _) -> 
         Option.some ("CSP: " ^
                        (match csp_script with
                        | List (Atom "SomeCSPSrc" :: src :: _) -> ("script-src " ^ (to_string src))
                        | _ -> "") ^ "; " ^
                        (match csp_tt with
                        | List (Atom "SomeTrustedTypes" :: List (Atom "Build_TrustedTypes" :: tt_policy :: tt_enforce :: _) :: _) ->
                            sprintf "%s%s"
                            (match tt_policy with
                             | List ( Atom "SomeoptionInt" :: Atom "NoneInt" :: _) -> "trusted-types; "
                             | List ( Atom "SomeoptionInt" :: policy :: _) -> sprintf "trusted-types %s; " (to_string policy)
                             | _ -> "")
                            (match tt_enforce with
                             | Atom "true" -> "require-trusted-types-for 'script'"
                             | _ -> "")
                        | _ -> ""))
       | _ -> None);
     ]
     |> cat_maybes |> String.concat "\\n"
  | _ -> failwith "Invalid ResponseHeaders"

let viz_rq_headers = function
  | List (Atom "Build_RequestHeaders" :: origin :: cookie :: referer :: _ ) ->
     [
       (match origin with
        | List (Atom "SomeOrigin" :: origin :: _) ->
           Option.some @@ "Origin: " ^ (url_to_origin_id origin)
        | _ -> None);
       (match referer with
        | List (Atom "SomeURL" :: url :: _) ->
           Option.some @@ "Referer: " ^ (url_to_origin_id url)
        | _ -> None);
     ]
     |> cat_maybes |> String.concat "\\n"
  | _ -> failwith "Invalid RequestHeaders"

let code_to_int = function
  | "ResponseOk" -> 200
  | "ResponseNoContent" -> 204
  | "ResponseFound" -> 302
  | "ResponseTemporaryRedirect" -> 307
  | _ -> failwith "Unknown ResponseCode"

let method_to_string = function
  | "MethodGet" -> "GET"
  | "MethodPost" -> "POST"
  | "MethodPut" -> "PUT"
  | "MethodDelete" -> "DELETE"
  | "MethodOptions" -> "OPTIONS"
  | _ -> failwith "Unknown Method"

let viz_request from = function
  | List (Atom "Build_Request" :: Atom rmethod :: url :: headers :: _) ->
     sprintf "%s -> %s: %s %s\\n%s" from (url_to_origin_id url)
       (method_to_string rmethod) (viz_url url) (viz_rq_headers headers)
  | _ -> failwith "Invalid Request"

let viz_response from = function
  | List (Atom "Build_Response" :: url :: Atom code :: headers :: _) ->
     sprintf "%s -> %s: %d %s\\n%s" (url_to_origin_id url) from
       (code_to_int code) code (viz_rp_headers headers)
  | _ -> failwith "Invalid Response"

let viz_dom_level = function
  | List (Atom "DOMPath" :: lst :: path :: _) ->
     sprintf "DOMPath %s %s" (list_notation lst) (to_string_hum path)
  | _ -> failwith "Invalid DOMPath"

let viz_event n st = function
  | Atom "EvInit" -> sprintf "%d. EvInit" n |> note_over "B"
  | List (Atom "EvDOMUpdate" :: domlevel :: _) ->
     sprintf "%d. EvDOMUpdate (%s)" n (viz_dom_level domlevel) |> note_over "B"
  | List (Atom "EvRequest" :: emitter :: request :: _ ) ->
     [ viz_request (emitter_from emitter) request;
       sprintf "%d. EvRequest (%s)" n (viz_emitter emitter) |> note_left
     ] |> String.concat "\n"
  | List (Atom "EvResponse" :: response :: _ ) ->
     [ viz_response (emitter_from (st_emitter st)) response;
       sprintf "%d. EvResponse (%s)" n (response_code response) |> note_left
     ] |> String.concat "\n"
  | List (Atom "EvWorkerCacheMatch" ::  Atom num :: _) ->
     [
       sprintf "%d. EvWorkerCacheMatch (%s)" n num |> note_over "SW";
       (* sprintf "SW -> JS: (responses gb).[%s]" num; *)
     ] |> String.concat "\n"
  | List (Atom "EvWorkerUpdateCache" ::  rq_idx :: rp_idx :: _) ->
     sprintf "%d. EvWorkerUpdateCache (%s) (%s)" n (to_string rq_idx) (to_string rp_idx) |> note_over "SW"
  | List (Atom "EvScriptUpdateCache" :: domlevel :: a :: b :: _) ->
     sprintf "%d. EvScriptUpdateCache (%s) %s %s" n (viz_dom_level domlevel) (to_string a) (to_string_hum b) |> note_over "JS"
  | List (Atom "EvScriptUpdateCache" :: args) ->
     sprintf "%d. EvScriptUpdateCache %s" n (Sexp.to_string_hum @@ List args) |> note_over "JS"
  | List (Atom "EvScriptSetCookie" :: dlfrom :: dlto :: c_idx :: setcookie :: _ ) ->
     sprintf "%d. EvScriptSetCookie (%s) (%s) %s \n(%s)" n (viz_dom_level dlfrom) (viz_dom_level dlto) (to_string c_idx) (viz_setcookie setcookie)
     |> note_over "JS"
  | List (Atom "EvScriptUpdateHTML" :: domlevel1 :: domlevel2 :: _ ) ->
     sprintf "%d. EvScriptUpdateHTML (%s) (%s)" n
       (viz_dom_level domlevel1) (viz_dom_level domlevel2)
     |> note_over "JS"

  | List (Atom "EvScriptDomainRelaxation" :: domlevel :: dom ::  _) ->
     sprintf "%d. EvScriptDomainRelaxation (%s) %s" n
       (viz_dom_level domlevel) (to_string_hum dom)
     |> note_over "JS"
  | List (Atom "EvScriptPostMessage" ::  _) ->
     sprintf "%d. EvScriptPostMessage" n |> note_over "JS"
  | List (Atom "EvScriptNavigateFrame" ::  dl1 :: dl2 :: _) ->
     sprintf "%d. EvScriptNavigateFrame (%s) (%s)" n (viz_dom_level dl1) (viz_dom_level dl2) |> note_over "JS"
  | List (Atom "EvScriptCreateBlobUrl" :: domlevel :: url :: _ ) ->
     sprintf "%d. EvScriptCreateBlobUrl (%s) (%s)"  n (viz_dom_level domlevel) (viz_url url)
     |> note_over "JS"
  | List (Atom "EvScriptStorageSetItem" :: pt :: org :: k :: v :: _ ) ->
     sprintf "%d. EvScriptStorageSetItem (%s) (%s) (%s) (%s)" n (viz_dom_level pt) (url_to_origin_id org) (to_string k) (to_string v)
     |> note_over "JS"
  | e -> failwith ("Invalid Event: " ^ (Sexp.to_string e))

let viz_state st = match st with
  | List (Atom "Build_State" :: Atom version :: event :: _)
    -> viz_event (int_of_string version) st event
  | _ -> failwith "Invalid State"

let viz lst =
  let states = List.map viz_state lst in
  let origins = List.map (fun ((pr, h, pt), name) ->
                    sprintf "%s := %s" name (List [Atom pr; h; pt] |> Sexp.to_string_hum))
                  (List.rev @@ origin_legend ()) in
  let domains = List.map (fun (domain, name) ->
                    sprintf "%s := %s" name (Sexp.to_string_hum domain)) (List.rev @@ domain_legend ()) in
  let legend = if origins <> [] then
                 [ "legend top right" ] @ origins @ domains @ [ "end legend" ]
               else []
  in
  [
      "@startuml";
      "skinparam monochrome true";
      "skinparam defaultTextAlignment center";
      "skinparam sequenceMessageAlign center";
      "box #dedede";
      "participant \"Browser\" as B";
      "participant \"JavaScript\" as JS";
      "participant \"ServiceWorker\" as SW";
      "end box"
    ]
  @ states @ legend
  @ ["@enduml"; ""]
  |> String.concat "\n"

end
