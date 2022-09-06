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

module Array : SP with type 'a t = 'a Model.Array.array
module Index : SP with type 'a t = 'a Model.Browser.coq_Index

module Int : S with type t = int
module String : S with type t = string
module Nonce : S with type t = Model.Browser.coq_Nonce
module Protocol : S with type t = Model.Browser.coq_Protocol
module Domain : S with type t = Model.Browser.coq_Domain
module Path : S with type t = Model.Browser.coq_Path
module Origin : S with type t = Model.Browser.coq_Origin
module URLPath : S with type t = Model.Browser.coq_URLPath
module URL : S with type t = Model.Browser.coq_URL
module Image : S with type t = Model.Browser.coq_Image
module Script : S with type t = Model.Browser.coq_Script
module RequestMethod : S with type t = Model.Browser.coq_RequestMethod
module Form : S with type t = Model.Browser.coq_Form
module Frame : S with type t = Model.Browser.coq_Frame
module HTMLElement : S with type t = Model.Browser.coq_HTMLElement
module HTMLHead : S with type t = Model.Browser.coq_HTMLHead
module HTMLBody : S with type t = Model.Browser.coq_HTMLBody
module HTML : S with type t = Model.Browser.coq_HTML
module ContentType : S with type t = Model.Browser.coq_ContentType
module ContentElement : S with type t = Model.Browser.coq_ContentElement
module DOMElement : S with type t = Model.Browser.coq_DOMElement
module DOMHead : S with type t = Model.Browser.coq_DOMHead
module DOMBody : S with type t = Model.Browser.coq_DOMBody
module DOM : S with type t = Model.Browser.coq_DOM
module CookieName : S with type t = Model.Browser.coq_CookieName
module CookieMapping : S with type t = Model.Browser.coq_CookieMapping
module SameSite : S with type t = Model.Browser.coq_SameSite
module SetCookie : S with type t = Model.Browser.coq_SetCookie
module Cookie : S with type t = Model.Browser.coq_Cookie
module RequestHeaders : S with type t = Model.Browser.coq_RequestHeaders
module Request : S with type t = Model.Browser.coq_Request
module CSPSrc : S with type t = Model.Browser.coq_CSPSrc
module TrustedTypes : S with type t = Model.Browser.coq_TrustedTypes
module CSP : S with type t = Model.Browser.coq_CSP
module ReferrerPolicy : S with type t = Model.Browser.coq_ReferrerPolicy
module ResponseHeaders : S with type t = Model.Browser.coq_ResponseHeaders
module ResponseCode : S with type t = Model.Browser.coq_ResponseCode
module Response : S with type t = Model.Browser.coq_Response
module DOMSelector : S with type t = Model.Browser.coq_DOMSelector
module NestedDOMPath : S with type t = Model.Browser.coq_NestedDOMPath
module Emitter : S with type t = Model.Browser.coq_Emitter
module FetchEngine : S with type t = Model.Browser.coq_FetchEngine
module ServiceWorker : S with type t = Model.Browser.coq_ServiceWorker
module Initiators : S with type t = Model.Browser.coq_Initiators
module Document : S with type t = Model.Browser.coq_Document
module Window : S with type t = Model.Browser.coq_Window
module Event : S with type t = Model.Browser.coq_Event
module Blob : S with type t = Model.Browser.coq_Blob
module StorageItem : S with type t = Model.Browser.coq_StorageItem


module State : S with type t = Model.Browser.coq_State
module Config : S with type t = Model.Browser.coq_Config
module Global : S with type t = Model.Browser.coq_Global
