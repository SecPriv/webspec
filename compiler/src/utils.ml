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

let equal_witness : type a b. a witness -> b witness -> (a,b) eq =
  fun u w ->
  match u, w with
  | Prop, Prop -> Eq
  | Set, Set -> Eq
  | _, _ -> Nq

type ident = string * string list

let kername_to_ident kn =
  let string = Names.KerName.to_string kn in
  match List.rev (String.split_on_char '.' string) with
  | hd :: tl -> hd, tl
  | [] -> assert false

let ident_to_string (hd, tl) =
  String.concat "." (List.rev (hd :: tl))

let pp_ident fmt ident = Format.fprintf fmt "%s" (ident_to_string ident)

module Name =
struct

  type t =
    | Anonymous
    | Id of int
    | Name of string

  let fresh = ref 0
  let fresh () = incr fresh; Id !fresh

  let compare (nm1: t)  (nm2: t) = compare nm1 nm2

  let equal nm1 nm2 =
    match nm1, nm2 with
    | Anonymous, Anonymous -> true
    | Id int1, Id int2 -> int1 = int2
    | Name string1, Name string2 -> String.equal string1 string2
    | _, _ -> false

  let of_string string =
    if String.equal "_" string then Anonymous
    else
      try Id (int_of_string String.(sub string 1 (length string - 2)))
      with _ -> Name string

  let to_string name =
    match name with
    | Anonymous -> Printf.sprintf "_"
    | Id int -> Printf.sprintf "<%i>" int
    | Name string -> string

  let pp fmt name = Format.fprintf fmt "%s" (to_string name)

end

type name = Name.t

module IntSet = Set.Make
    (struct
      type t = int
      let compare i1 i2 = compare i1 i2
    end)

module IntMap = Map.Make
    (struct
      type t = int
      let compare i1 i2 = compare i1 i2
    end)

module IntHashtbl = Hashtbl.Make
    (struct
      type t = int
      let equal i1 i2 = i1 = i2
      let hash i = i
    end)

module StringSet = Set.Make
    (struct
      type t = string
      let compare s1 s2 = String.compare s1 s2
    end)

module StringMap = Map.Make
    (struct
      type t = string
      let compare s1 s2 = String.compare s1 s2
    end)

module StringHashtbl = Hashtbl.Make
    (struct
      type t = string
      let equal s1 s2 = String.equal s1 s2
      let hash s = Hashtbl.hash s
    end)

module NameSet = Set.Make
    (struct
      type t = name
      let compare nm1 nm2 = Name.compare nm1 nm2
    end)

module NameMap = Map.Make
    (struct
      type t = name
      let compare nm1 nm2 = Name.compare nm1 nm2
    end)

module List =
struct
  include Stdlib.List

  let rec drop n list =
    if n > 0 then
      match list with
      | _ :: list -> drop (n-1) list
      | [] -> []
    else list

  let rec take n list =
    if n > 0 then
      match list with
      | x :: list -> x :: take (n-1) list
      | [] -> []
    else []

end
