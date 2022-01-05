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

type ('a,'b) msg = (('a, Format.formatter, unit, 'b) format4 -> 'a) -> 'b

module type SRC =
sig
  val name : string

  val info    : unit -> bool
  val debug   : unit -> bool
  val warning : unit -> bool
  val error   : unit -> bool
end

module type LOG =
sig
  val info    : ('a,unit) msg -> unit
  val debug   : ('a,unit) msg -> unit
  val warning : ('a,unit) msg -> unit
  val error   : ('a,unit) msg -> unit

  module Verbose :
  sig
    type ('a,'b) verbose =
      head:('a,unit) msg ->
      body:('b,unit) msg -> unit

    val info    : ('a,'b) verbose
    val debug   : ('a,'b) verbose
    val warning : ('a,'b) verbose
    val error   : ('a,'b) verbose
  end
end

module Make (Src:SRC) : LOG
module Default (Src : sig val name : string end) : LOG
