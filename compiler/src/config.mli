(********************************************************************************)
(*  Copyright (c) 2021 Benjamin Farinier                                        *)
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

module Env :
sig

  module type ARG =
  sig
    type t

    val name : string
    val doc  : string
    val default : t

    val get : unit -> t
  end

  module type BOOL   = ARG with type t = bool
  module type INT    = ARG with type t = int
  module type FLOAT  = ARG with type t = float
  module type STRING = ARG with type t = string

  module Bool
      (Arg : sig
         val name : string
         val doc  : string
         val default : bool
       end) : BOOL

  module Int
      (Arg : sig
         val name : string
         val doc  : string
         val default : int
       end) : INT

  module Float
      (Arg : sig
         val name : string
         val doc  : string
         val default : float
       end) : FLOAT

  module String
      (Arg : sig
         val name : string
         val doc  : string
         val default : string
       end) : STRING

end

(********************************************************************************)

module Coq :
sig

  module type ARG =
  sig
    type t

    val default : t
    val set : t -> unit
    val get : unit -> t
  end

  module type BOOL   = ARG with type t = bool
  module type INT    = ARG with type t = int
  module type FLOAT  = ARG with type t = float
  module type STRING = ARG with type t = string

  module type SET =
  sig
    type elt

    val clear  : unit -> unit
    val add    : elt -> unit
    val mem    : elt -> bool
    val remove : elt -> unit

    val elements : unit -> elt list
  end

  module Set
      (Ord : sig
         type t
         val compare : t -> t -> int
       end) : SET with type elt = Ord.t

  module type MAP =
  sig
    type key
    type elt

    val clear  : unit -> unit
    val add    : key -> elt -> unit
    val find   : key -> elt option
    val remove : key -> unit

    val bindings : unit -> (key * elt) list
  end

  module Map
      (Ord : sig
         type t
         val compare : t -> t -> int
       end)
      (Elt : sig type t end) :
    MAP with type key = Ord.t
         and type elt = Elt.t

end

(********************************************************************************)

module Info    : Env.BOOL
module Debug   : Env.BOOL
module Warning : Env.BOOL
module Error   : Env.BOOL

module ArraySize   : Coq.INT
module InlineDepth : Coq.INT

module InlinedConstants : Coq.SET with type elt = Names.KerName.t
module InlinedRelations : Coq.MAP with type key = string and type elt = int
module DestructRelations: Coq.MAP with type key = string and type elt = int
