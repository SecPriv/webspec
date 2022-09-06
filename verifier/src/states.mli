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
  blob : Types.URL.t option
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


  val update_ports : t -> Types.Protocol.t -> int -> t
  val update_domains :  t -> Types.Domain.t -> t
  val update_origins :  t -> Types.Origin.t -> t
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

module VerifierState : S with type t = verifier_state
