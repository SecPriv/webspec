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

val get_constructor : Ast.datatype -> int -> Ast.constructor
val get_selector    : Ast.datatype -> int -> int -> Ast.selector

val get_name : Ast.t -> string
val sort_to_string : _ Ast.sort -> string

val subst_sort : (string -> Ast.set Ast.sort) -> 'a Ast.sort -> 'a Ast.sort
val subst_term : (string -> Ast.set Ast.sort) -> (Ast.var -> Ast.set Ast.term) ->
  'a Ast.term -> 'a Ast.term

val subst_sort_list : (string * Ast.set Ast.sort) list -> 'a Ast.sort -> 'a Ast.sort
val subst_term_list : (string * Ast.set Ast.sort) list -> (Ast.var * Ast.set Ast.term) list ->
  'a Ast.term -> 'a Ast.term

(******************************************************************************)

type ('a,'b) fn = before:'a -> after:'a -> 'b -> 'a * 'b

type 'a bind = {
  bind_sort : (string, 'a) fn;
  bind_decl : (Ast.var, 'a) fn;
  bind_defn : (Ast.var * Ast.set Ast.term, 'a) fn;
  unbind_sort : (string, 'a) fn;
  unbind_decl : (Ast.var, 'a) fn;
  unbind_defn : (Ast.var * Ast.set Ast.term, 'a) fn;
}

val bind_identity : 'a bind

type 'a fold_map = {
  fold_map_sort : 'b. ('b Ast.sort, 'a) fn;
  fold_map_term : 'b. ('b Ast.term, 'a) fn;
  fold_map_dttp : (Ast.datatype, 'a) fn;
  fold_map_sdef : (Ast.sortdefn,  'a) fn;
  fold_map_fdec : 'b. ('b Ast.fundecl, 'a) fn;
  fold_map_fdef : 'b. ('b Ast.fundefn, 'a) fn;
  fold_map_var  : (Ast.var, 'a) fn;
}

val fold_map_identity : 'a fold_map

val fold_map_sort : 'a bind -> 'a fold_map -> 'b Ast.sort -> 'a -> 'b Ast.sort * 'a
val fold_map_term : 'a bind -> 'a fold_map -> 'b Ast.term -> 'a -> 'b Ast.term * 'a
val fold_map_dttp : 'a bind -> 'a fold_map -> Ast.datatype -> 'a -> Ast.datatype * 'a

val fold_map : 'a bind -> 'a fold_map -> Ast.t -> 'a -> Ast.t * 'a

