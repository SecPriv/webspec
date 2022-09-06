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

type 'a error_or = ('a, string) result

module type S =
sig
  type t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val of_yojson : Yojson.Safe.t -> (t, string) result
  val to_yojson : t -> Yojson.Safe.t

  module Set : Set.S with type elt = t 
  module Map : Map.S with type key = t 

end

module type SP =
sig
  type 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

  val equal :('a -> 'a -> Ppx_deriving_runtime.bool) ->
    'a t -> 'a t -> Ppx_deriving_runtime.bool
  val compare :('a -> 'a -> Ppx_deriving_runtime.int) ->
    'a t -> 'a t -> Ppx_deriving_runtime.int

  val of_yojson : (Yojson.Safe.t -> 'a error_or) ->
    Yojson.Safe.t -> 'a t error_or
  val to_yojson : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t

end

module Int : S with type t = int =
struct

  module Internal =
  struct

    type t = int
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal) 
  module Map = Map.Make(Internal) 

end

module String : S with type t = string =
struct

  module Internal =
  struct

    type t = string
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal) 
  module Map = Map.Make(Internal) 

end


type 'a coq_Index = [%import: 'a Model.Browser.coq_Index] [@@deriving yojson, eq, ord, show]
module Index : SP with type 'a t = 'a Model.Browser.coq_Index =
struct
  type 'a t = 'a coq_Index
  [@@deriving show, eq, ord, yojson]

end

module Array : SP with type 'a t = 'a Model.Array.array =
struct
  type 'a t = [%import: 'a Model.Array.array]
  [@@deriving show, eq, ord, yojson]

end

type coq_Nonce = [%import: Model.Browser.coq_Nonce][@@deriving show, eq, ord, yojson]
module Nonce : S with type t = Model.Browser.coq_Nonce =
struct

  module Internal =
  struct

    type t = coq_Nonce
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Protocol = [%import: Model.Browser.coq_Protocol][@@deriving show, eq, ord, yojson]
module Protocol : S with type t = Model.Browser.coq_Protocol =
struct

  module Internal =
  struct

    type t = coq_Protocol
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (proto : coq_Protocol) : string =
    Printf.sprintf "%s" (
      match proto with 
      | ProtocolHTTP -> "http"
      | ProtocolHTTPS -> "https"
      | ProtocolData -> "data"
      | ProtocolBlob -> "blob"
    )

  let pp (fmt) (proto : coq_Protocol) : unit =
    Format.fprintf fmt "%s" (show proto)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Domain = [%import: Model.Browser.coq_Domain][@@deriving show, eq, ord, yojson]
module Domain : S with type t = Model.Browser.coq_Domain =
struct

  module Internal =
  struct

    type t = coq_Domain
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (domain : coq_Domain) : string =
    match domain with
    | Coq_domain (d) -> Printf.sprintf "%d.test" d
    | Coq_subdomain (s, d) -> Printf.sprintf "%s.%s.test" (string_of_int s) (string_of_int d)

  let pp (fmt) (dmn : coq_Domain) : unit =
    Format.fprintf fmt "%s" (show dmn)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Path = [%import: Model.Browser.coq_Path][@@deriving show, eq, ord, yojson]
module Path : S with type t = Model.Browser.coq_Path =
struct

  module Internal =
  struct

    type t = coq_Path
    [@@deriving show, eq, ord, yojson]

  end

  include Internal

  let show (path : coq_Path) : string =
    match path with 
    | Coq_slash -> "/"
    | Coq_anypath (i) -> "/" ^ (string_of_int i)

  let pp (fmt) (path : coq_Path) : unit =
    Format.fprintf fmt "%s" (show path)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Origin = [%import: Model.Browser.coq_Origin][@@deriving show, eq, ord, yojson]
module Origin : S with type t = Model.Browser.coq_Origin =
struct

  module Internal =
  struct

    type t = coq_Origin
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (origin : coq_Origin) : string =
    match origin with
    | TupleOrigin (proto, dom, port) -> (
      Printf.sprintf "%s://%s%s" 
        (Protocol.show proto)
        (Option.value ~default:"" (Option.bind dom (fun d -> Some(Domain.show d))))
        (Option.value ~default:"" (Option.bind port (fun p -> Some(Printf.sprintf ":%d" p))))
    )
    | OpaqueOrigin (nonce) -> string_of_int nonce 

let pp (fmt) (origin : coq_Origin) : unit =
  Format.fprintf fmt "%s" (show origin)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_URLPath = [%import: Model.Browser.coq_URLPath][@@deriving show, eq, ord, yojson]
module URLPath : S with type t = Model.Browser.coq_URLPath =
struct

  module Internal =
  struct

    type t = coq_URLPath
    [@@deriving eq, ord, yojson]

  end

  include Internal


  let show (path : coq_URLPath) : string =
    match path with 
    | Coq_url_path_data (nonce, id) -> (string_of_int nonce) 
    | Coq_url_path_blob (origin, nonce) -> (
      Printf.sprintf "%s/%d" 
        (Origin.show origin)
        (nonce)
    )
    | Coq_url_path_res (path) -> (
      match path with
      | Coq_slash -> ""
      | Coq_anypath (i) -> string_of_int i
    )

  let show_with_context (gb : Model.Browser.coq_Global) (st : Model.Browser.coq_State) (path : coq_URLPath) : string =
    match path with 
    | Coq_url_path_data (nonce, id) -> (string_of_int nonce) 
    | Coq_url_path_blob (origin, nonce) -> (
      Printf.sprintf "%s/%d" 
        (Origin.show origin)
        (nonce)
    )
    | Coq_url_path_res (path) -> (
      match path with
      | Coq_slash -> ""
      | Coq_anypath (i) -> Printf.sprintf "%d" i
    )

  let pp (fmt) (path : coq_URLPath) : unit =
    Format.fprintf fmt "%s" (show path)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_URL = [%import: Model.Browser.coq_URL][@@deriving show, eq, ord, yojson]
module URL : S with type t = Model.Browser.coq_URL =
struct

  module Internal =
  struct

    type t = coq_URL
    [@@deriving eq, ord, yojson]

  end

  include Internal


  let show (url : coq_URL) : string =
    (* match the url with the correct protocol/path pair *)
    match url with 
    | {url_protocol=ProtocolHTTP; url_host=_; url_port=_; url_path=(Coq_url_path_res (_))}
    | {url_protocol=ProtocolHTTPS; url_host=_; url_port=_; url_path=(Coq_url_path_res (_))} -> (
      Printf.sprintf "%s://%s%s/%s%s" 
        (Protocol.show url.url_protocol)
        (Option.value ~default:"" (Option.bind url.url_host (fun domain -> Some(Domain.show domain))))
        (Option.value ~default:"" (Option.bind url.url_port (fun port -> Some(Printf.sprintf ":%d" port))))
        ("verifier/server.py") (* maybe have a config file  to speciy these constants*)
        (if (URLPath.show url.url_path) = "" then "" else "?res=" ^ (URLPath.show url.url_path))
    )
    | {url_protocol=ProtocolData; url_host=_; url_port=_; url_path=(Coq_url_path_data (_, _))} -> (
        Printf.sprintf "data:,%s" (URLPath.show url.url_path)
    )
    | {url_protocol=ProtocolBlob; url_host=_; url_port=_; url_path=(Coq_url_path_blob (_, _))} -> (
        Printf.sprintf "blob:%s" (URLPath.show url.url_path)
    )
    | _ -> ""


let pp (fmt) (url : coq_URL) : unit =
  Format.fprintf fmt "%s" (show url)



  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Image = [%import: Model.Browser.coq_Image][@@deriving show, eq, ord, yojson]
module Image : S with type t = Model.Browser.coq_Image =
struct

  module Internal =
  struct

    type t = coq_Image
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Script = [%import: Model.Browser.coq_Script][@@deriving show, eq, ord, yojson]
module Script : S with type t = Model.Browser.coq_Script =
struct

  module Internal =
  struct

    type t = coq_Script
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_RequestMethod = [%import: Model.Browser.coq_RequestMethod][@@deriving show, eq, ord, yojson]
module RequestMethod : S with type t = Model.Browser.coq_RequestMethod =
struct

  module Internal =
  struct

    type t = coq_RequestMethod
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (methd : coq_RequestMethod) : string =
    Printf.sprintf "%s" (
      match methd with 
      | MethodGet -> "GET"
      | MethodPost -> "POST"
      | MethodPut -> "PUT"
      | MethodDelete -> "DELETE"
      | MethodOptions -> "OPTIONS"
    )

  let pp (fmt) (methd : coq_RequestMethod) : unit =
    Format.fprintf fmt "%s" (show methd)


  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Form = [%import: Model.Browser.coq_Form][@@deriving show, eq, ord, yojson]
module Form : S with type t = Model.Browser.coq_Form =
struct

  module Internal =
  struct

    type t = coq_Form
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Frame = [%import: Model.Browser.coq_Frame][@@deriving show, eq, ord, yojson]
module Frame : S with type t = Model.Browser.coq_Frame =
struct

  module Internal =
  struct

    type t = coq_Frame
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_HTMLElement = [%import: Model.Browser.coq_HTMLElement][@@deriving show, eq, ord, yojson]
module HTMLElement : S with type t = Model.Browser.coq_HTMLElement =
struct

  module Internal =
  struct

    type t = coq_HTMLElement
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_HTMLHead = [%import: Model.Browser.coq_HTMLHead][@@deriving show, eq, ord, yojson]
module HTMLHead : S with type t = Model.Browser.coq_HTMLHead =
struct

  module Internal =
  struct

    type t = coq_HTMLHead
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_HTMLBody = [%import: Model.Browser.coq_HTMLBody][@@deriving show, eq, ord, yojson]
module HTMLBody : S with type t = Model.Browser.coq_HTMLBody =
struct

  module Internal =
  struct

    type t = coq_HTMLBody
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_HTML = [%import: Model.Browser.coq_HTML][@@deriving show, eq, ord, yojson]
module HTML : S with type t = Model.Browser.coq_HTML =
struct

  module Internal =
  struct

    type t = coq_HTML
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ContentType = [%import: Model.Browser.coq_ContentType][@@deriving show, eq, ord, yojson]
module ContentType : S with type t = Model.Browser.coq_ContentType =
struct

  module Internal =
  struct

    type t = coq_ContentType
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (ctype : coq_ContentType) : string =
    match ctype with 
    | ContentTypeHTML -> "text/html"
    | ContentTypeImage -> "image/bmp"
    | ContentTypeScript -> "application/x-javascript"

  let pp (fmt) (ctype : coq_ContentType) : unit =
    Format.fprintf fmt "%s" (show ctype)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ContentElement = [%import: Model.Browser.coq_ContentElement][@@deriving show, eq, ord, yojson]
module ContentElement : S with type t = Model.Browser.coq_ContentElement =
struct

  module Internal =
  struct

    type t = coq_ContentElement
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_DOMElement = [%import: Model.Browser.coq_DOMElement][@@deriving show, eq, ord, yojson]
module DOMElement : S with type t = Model.Browser.coq_DOMElement =
struct

  module Internal =
  struct

    type t = coq_DOMElement
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_DOMHead = [%import: Model.Browser.coq_DOMHead][@@deriving show, eq, ord, yojson]
module DOMHead : S with type t = Model.Browser.coq_DOMHead =
struct

  module Internal =
  struct

    type t = coq_DOMHead
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_DOMBody = [%import: Model.Browser.coq_DOMBody][@@deriving show, eq, ord, yojson]
module DOMBody : S with type t = Model.Browser.coq_DOMBody =
struct

  module Internal =
  struct

    type t = coq_DOMBody
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_DOM = [%import: Model.Browser.coq_DOM][@@deriving show, eq, ord, yojson]
module DOM : S with type t = Model.Browser.coq_DOM =
struct

  module Internal =
  struct

    type t = coq_DOM
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_CookieName = [%import: Model.Browser.coq_CookieName][@@deriving show, eq, ord, yojson]
module CookieName : S with type t = Model.Browser.coq_CookieName =
struct

  module Internal =
  struct

    type t = coq_CookieName
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (name : coq_CookieName) : string =
    match name with 
    | NoPrefix (x) -> Printf.sprintf "%d" x
    | Secure (x) -> Printf.sprintf "__Secure-%d" x
    | Host (x) -> Printf.sprintf "__Host-%d" x

  let pp (fmt) (name : coq_CookieName) : unit =
    Format.fprintf fmt "%s" (show name)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_CookieMapping = [%import: Model.Browser.coq_CookieMapping][@@deriving show, eq, ord, yojson]
module CookieMapping : S with type t = Model.Browser.coq_CookieMapping =
struct

  module Internal =
  struct

    type t = coq_CookieMapping
    [@@deriving eq, ord, yojson]

  end

  let show (cookie : coq_CookieMapping) : string =
    Printf.sprintf "%s=%d" 
      (CookieName.show cookie.cm_name)
      (cookie.cm_value)

  let pp (fmt) (cookie : coq_CookieMapping) : unit =
    Format.fprintf fmt "%s" (show cookie)

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_SameSite = [%import: Model.Browser.coq_SameSite][@@deriving show, eq, ord, yojson]
module SameSite : S with type t = Model.Browser.coq_SameSite =
struct

  module Internal =
  struct

    type t = coq_SameSite
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (ss : coq_SameSite) : string =
    match ss with 
    | SSStrict -> "Strict"
    | SSLax -> "Lax"
    | SSNone -> "None"

  let pp (fmt) (ss : coq_SameSite) : unit =
    Format.fprintf fmt "%s" (show ss)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_SetCookie = [%import: Model.Browser.coq_SetCookie][@@deriving show, eq, ord, yojson]
module SetCookie : S with type t = Model.Browser.coq_SetCookie =
struct

  module Internal =
  struct

    type t = coq_SetCookie
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (cookie : coq_SetCookie) : string =
    (* Set-Cookie: <cookie-name>=<cookie-value>; Domain=<domain-value>; Secure; HttpOnly ; Path=/*)
    Printf.sprintf "%s=%d;%s%s%s%s%s" 
      (CookieName.show cookie.sc_name)
      (cookie.sc_value)
      (match cookie.sc_domain with | None -> "" | Some(d) -> Printf.sprintf " Domain=%s;" (Domain.show d))
      (Printf.sprintf " Path=%s;" (Path.show cookie.sc_path))
      (if cookie.sc_secure then " Secure;" else "")
      (if cookie.sc_http_only then " HttpOnly;" else "")
      (Printf.sprintf " SameSite=%s;" (SameSite.show cookie.sc_same_site))

  let pp (fmt) (cookie : coq_SetCookie) : unit =
    Format.fprintf fmt "%s" (show cookie)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Cookie = [%import: Model.Browser.coq_Cookie][@@deriving show, eq, ord, yojson]
module Cookie : S with type t = Model.Browser.coq_Cookie =
struct

  module Internal =
  struct

    type t = coq_Cookie
    [@@deriving show, eq, ord, yojson]

  end

  include Internal


  let show (cookie : coq_Cookie) : string =
    (* ignoring the list order (should be ordered regardless)*)
    let repr = StdLabels.String.concat ~sep:"; " (List.fold_left (fun acc (idx, v) -> (
      match (idx, v) with
      | (_, Some(v)) -> acc @ [(CookieMapping.show v)]
      | _ -> acc
    )) [] cookie) in

    if (StdLabels.String.length repr) > 0  then (
      StdLabels.String.sub repr ~pos:0 ~len:((StdLabels.String.length repr) - 2)
    ) else (
      ""
    )

  let pp (fmt) (cookie : coq_Cookie) : unit =
    Format.fprintf fmt "%s" (show cookie)


  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_RequestHeaders = [%import: Model.Browser.coq_RequestHeaders][@@deriving show, eq, ord, yojson]
module RequestHeaders : S with type t = Model.Browser.coq_RequestHeaders =
struct

  module Internal =
  struct

    type t = coq_RequestHeaders
    [@@deriving eq, ord, of_yojson]

  end

  let to_yojson (headers : coq_RequestHeaders) : Yojson.Safe.t = 
    `Assoc (
      List.filter (fun (k,v) -> ( v <> `Null) ) 
      [
        ("Origin", 
        match headers.rq_hd_origin with
        | None -> `Null 
        | Some(hd) -> `String (Origin.show hd)) ;
        ("Cookie", (
          match (Cookie.show headers.rq_hd_cookie) with
          | "" -> `Null
          | str -> `String str
          )) ;
        ("Referer", 
        match headers.rq_hd_referer with
        | None -> `Null
        | Some(hd) -> `String (URL.show hd)) ;
      ]
    )

  let show (headers : coq_RequestHeaders) : string =
    Printf.sprintf "%s%s%s" 
      (match headers.rq_hd_origin with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Origin: %s\n" (Origin.show hd))
      (Printf.sprintf "Cookie: %s\n" (Cookie.show headers.rq_hd_cookie))
      (match headers.rq_hd_referer with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Referer: %s\n" (URL.show hd))

  let pp (fmt) (hdrs : coq_RequestHeaders) : unit =
    Format.fprintf fmt "%s" (show hdrs)

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Request = [%import: Model.Browser.coq_Request][@@deriving show, eq, ord, yojson]
module Request : S with type t = Model.Browser.coq_Request =
struct

  module Internal =
  struct

    type t = coq_Request
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_CSPSrc = [%import: Model.Browser.coq_CSPSrc][@@deriving show, eq, ord, yojson]
module CSPSrc : S with type t = Model.Browser.coq_CSPSrc =
struct

  module Internal =
  struct

    type t = coq_CSPSrc
    [@@deriving eq, ord, yojson]

  end
  include Internal


  let show (src : coq_CSPSrc) : string =
    match src with 
    | CSPSrcNone -> "'none'"
    | CSPSrcSelf -> "'self'"
    | CSPSrcScheme (proto) -> Protocol.show proto ^ ":"
    | CSPSrcSource (proto, subd, dom, port, path) ->
      (
        let domain = 
          match (subd : int option option) with 
          | None -> Printf.sprintf "%s" @@ Domain.show (Coq_domain(dom))
          | Some (None) -> Printf.sprintf "*.%s" @@ Domain.show (Coq_domain (dom))
          | Some (Some (s)) -> Printf.sprintf "%s" @@ Domain.show @@ (Coq_subdomain (s, dom))
        in
        Printf.sprintf "%s%s%s%s" 
        ( match proto with 
          | None -> ""
          | Some (p) -> (Protocol.show p) ^ "://"
        )
        ( domain )
        ( match port with
          | None -> ":*"
          | Some (p) -> ":" ^ (string_of_int p)
        )
        ( 
          ""
        ) 
      )
    


  let pp (fmt) (src : coq_CSPSrc) : unit =
    Format.fprintf fmt "%s" (show src)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_TrustedTypes = [%import: Model.Browser.coq_TrustedTypes][@@deriving show, eq, ord, yojson]
module TrustedTypes : S with type t = Model.Browser.coq_TrustedTypes =
struct

  module Internal =
  struct

    type t = coq_TrustedTypes
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_CSP = [%import: Model.Browser.coq_CSP][@@deriving show, eq, ord, yojson]
module CSP : S with type t = Model.Browser.coq_CSP =
struct

  module Internal =
  struct

    type t = coq_CSP
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (csp : coq_CSP) : string =
    let scr_src = 
      match csp.csp_script_src with
      | None -> ""  
      | Some (src) -> Printf.sprintf "script-src %s; " (CSPSrc.show src)
    in
    let req = match csp.csp_trusted_types with 
    | None -> "" 
    | Some (tt) -> 
      let r1 = if tt.tt_require_for_script then " require-trusted-types-for 'script';" else "" in
      let r2 = 
        match tt.tt_policy with
        | None -> ""
        | Some (None) -> " trusted-types;"
        | Some (Some (v)) -> Printf.sprintf " trusted-types %d;" v
      in
      r1 ^ r2
    in 

    Printf.sprintf "%s%s" scr_src req


  let pp (fmt) (csp : coq_CSP) : unit =
    Format.fprintf fmt "%s" (show csp)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ReferrerPolicy = [%import: Model.Browser.coq_ReferrerPolicy][@@deriving show, eq, ord, yojson]
module ReferrerPolicy : S with type t = Model.Browser.coq_ReferrerPolicy =
struct

  module Internal =
  struct

    type t = coq_ReferrerPolicy
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ResponseHeaders = [%import: Model.Browser.coq_ResponseHeaders][@@deriving show, eq, ord, yojson]
module ResponseHeaders : S with type t = Model.Browser.coq_ResponseHeaders =
struct

  module Internal =
  struct

    type t = coq_ResponseHeaders
    [@@deriving eq, ord, of_yojson]

  end

  include Internal

  let to_yojson (headers : coq_ResponseHeaders) : Yojson.Safe.t = 
    `Assoc (
      List.filter (fun (k,v) -> ( v <> `Null) ) 
      [
      ("Content-Type", 
      match headers.rp_hd_content_type with
      | None -> `Null 
      | Some(hd) -> `String (ContentType.show hd)) ;
      ("Set-Cookie", 
      match headers.rp_hd_set_cookie with
      | None -> `Null
      | Some(hd) -> `String (SetCookie.show hd)) ;
      ("Access-Control-Allow-Origin", 
      match headers.rp_hd_access_control_allow_origin with
      | None -> `Null
      | Some(hd) -> `String (Origin.show hd)) ;
      ("Location", 
      match headers.rp_hd_location with
      | None -> `Null
      | Some(hd) -> (
        match URL.show hd with 
        | "" -> `Null (* URL IS NOT VALID: IGNORE FIELD *)
        | str -> `String str
        )
      ) ;
      ("Content-Security-Policy", 
      match headers.rp_hd_csp with
      | None -> `Null
      | Some(hd) -> (
        match (CSP.show hd) with
        | "" -> `Null
        | str -> `String (str)
      )) ;
      ("Referrer-Policy", 
      match headers.rp_hd_referrer_policy with
      | None -> `Null
      | Some(hd) -> `String (ReferrerPolicy.show hd)) ;
    ])

  let show (headers : coq_ResponseHeaders) : string =
    Printf.sprintf "%s%s%s%s%s%s" 
      (match headers.rp_hd_content_type with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Content-Type: %s\n" (ContentType.show hd))
      (match headers.rp_hd_set_cookie with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Set-Cookie: %s\n" (SetCookie.show hd))
      (match headers.rp_hd_access_control_allow_origin with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Access-Control-Allow-Origin: %s\n" (Origin.show hd))
      (match headers.rp_hd_location with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Location: %s\n" (URL.show hd))
      (match headers.rp_hd_csp with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Content-Security-Policy: %s\n" (CSP.show hd))
      (match headers.rp_hd_referrer_policy with
      | None -> ""
      | Some(hd) -> Printf.sprintf "Referrer-Policy: %s\n" (ReferrerPolicy.show hd))
    
  let pp (fmt) (headers : coq_ResponseHeaders) : unit =
    Format.fprintf fmt "%s" (show headers)


  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ResponseCode = [%import: Model.Browser.coq_ResponseCode][@@deriving show, eq, ord, yojson]
module ResponseCode : S with type t = Model.Browser.coq_ResponseCode =
struct

  module Internal =
  struct

    type t = coq_ResponseCode
    [@@deriving eq, ord, yojson]

  end

  include Internal

  let show (code : coq_ResponseCode) : string =
    match code with 
    | ResponseOk -> "200" (* OK *)
    | ResponseNoContent -> "204" (* No Content *)
    | ResponseFound -> "404" (* Not Found *)
    | ResponseTemporaryRedirect -> "307" (* Temporary Redirect *)

  let pp (fmt) (code : coq_ResponseCode) : unit =
    Format.fprintf fmt "%s" (show code)

  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Response = [%import: Model.Browser.coq_Response][@@deriving show, eq, ord, yojson]
module Response : S with type t = Model.Browser.coq_Response =
struct

  module Internal =
  struct

    type t = coq_Response
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_DOMSelector = [%import: Model.Browser.coq_DOMSelector][@@deriving show, eq, ord, yojson]
module DOMSelector : S with type t = Model.Browser.coq_DOMSelector =
struct

  module Internal =
  struct

    type t = coq_DOMSelector
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_NestedDOMPath = [%import: Model.Browser.coq_NestedDOMPath][@@deriving show, eq, ord, yojson]
module NestedDOMPath : S with type t = Model.Browser.coq_NestedDOMPath =
struct

  module Internal =
  struct

    type t = coq_NestedDOMPath
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Emitter = [%import: Model.Browser.coq_Emitter][@@deriving show, eq, ord, yojson]
module Emitter : S with type t = Model.Browser.coq_Emitter =
struct

  module Internal =
  struct

    type t = coq_Emitter
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_FetchEngine = [%import: Model.Browser.coq_FetchEngine][@@deriving show, eq, ord, yojson]
module FetchEngine : S with type t = Model.Browser.coq_FetchEngine =
struct

  module Internal =
  struct

    type t = coq_FetchEngine
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_ServiceWorker = [%import: Model.Browser.coq_ServiceWorker][@@deriving show, eq, ord, yojson]
module ServiceWorker : S with type t = Model.Browser.coq_ServiceWorker =
struct

  module Internal =
  struct

    type t = coq_ServiceWorker
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Initiators = [%import: Model.Browser.coq_Initiators][@@deriving show, eq, ord, yojson]
module Initiators : S with type t = Model.Browser.coq_Initiators =
struct

  module Internal =
  struct

    type t = coq_Initiators
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Document = [%import: Model.Browser.coq_Document][@@deriving show, eq, ord, yojson]
module Document : S with type t = Model.Browser.coq_Document =
struct

  module Internal =
  struct

    type t = coq_Document
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Window = [%import: Model.Browser.coq_Window][@@deriving show, eq, ord, yojson]
module Window : S with type t = Model.Browser.coq_Window =
struct

  module Internal =
  struct

    type t = coq_Window
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Event = [%import: Model.Browser.coq_Event][@@deriving show, eq, ord, yojson]
module Event : S with type t = coq_Event =
struct

  module Internal =
  struct

    type t = coq_Event
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Blob = [%import: Model.Browser.coq_Blob][@@deriving show, eq, ord, yojson]
module Blob : S with type t = Model.Browser.coq_Blob =
struct

  module Internal =
  struct

    type t = coq_Blob
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_StorageItem = [%import: Model.Browser.coq_StorageItem][@@deriving show, eq, ord, yojson]
module StorageItem : S with type t = Model.Browser.coq_StorageItem =
struct

  module Internal =
  struct

    type t = coq_StorageItem
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_State = [%import: Model.Browser.coq_State][@@deriving show, eq, ord, yojson]
module State : S with type t = Model.Browser.coq_State =
struct

  module Internal =
  struct

    type t = coq_State
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Config = [%import: Model.Browser.coq_Config][@@deriving show, eq, ord, yojson]
module Config : S with type t = Model.Browser.coq_Config =
struct

  module Internal =
  struct

    type t = coq_Config
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

type coq_Global = [%import: Model.Browser.coq_Global][@@deriving show, eq, ord, yojson]
module Global : S with type t = Model.Browser.coq_Global =
struct

  module Internal =
  struct

    type t = coq_Global
    [@@deriving show, eq, ord, yojson]

  end

  include Internal
  module Set = Set.Make(Internal)
  module Map = Map.Make(Internal)

end

