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

type set
type prop


type (_,_) eq = Eq : ('a,'a) eq | Nq : ('a,'b) eq

type _ witness = Prop : prop witness | Set : set witness

val equal_witness : 'a witness -> 'b witness -> ('a,'b) eq


type ident = string * string list

val kername_to_ident : Names.KerName.t -> ident
val ident_to_string  : ident -> string

val pp_ident : Format.formatter -> ident -> unit


module Name :
sig
  type t =
    | Anonymous
    | Id of int
    | Name of string

  val fresh : unit -> t
  val equal : t -> t -> bool
  val of_string : string -> t
  val to_string : t -> string
  val pp : Format.formatter -> t -> unit
end

type name = Name.t


module IntSet : Set.S with type elt = int
module IntMap : Map.S with type key = int
module IntHashtbl : Hashtbl.S with type key = int

module StringSet : Set.S with type elt = string
module StringMap : Map.S with type key = string
module StringHashtbl : Hashtbl.S with type key = string

module NameSet : Set.S with type elt = name
module NameMap : Map.S with type key = name

module List :
sig
  include module type of List

  val drop : int -> 'a list -> 'a list
  val take : int -> 'a list -> 'a list
end
