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

open Utils

type recursivity_kind =
  | Finite
  | CoFinite
  | BiFinite

type sort = Prop | Set | Type

type term = private {
  term_hash : int;
  term_desc : term_desc;
}

and term_desc =
  | Rel       of name
  | Sort      of sort
  | Product   of name * typ * typ
  | Lambda    of name * typ * term
  | LetIn     of name * term * typ * term
  | App       of term * term array
  | Constant  of constant
  | Inductive of (inductive * int)
  | Construct of (inductive * int) * int
  | Project   of projection * term
  | Case      of case * term * typ * term array
  | Int       of int
  | Float     of float
  | Array     of term array * term * typ
  | Primitive of Primitive.t * typ

and typ = term

and constant = private {
  cnst_hash : int;
  cnst_ident: ident;
  cnst_type : typ;
  cnst_body : term option;
}

and inductive = private {
  indv_hash  : int;
  indv_ident : ident;
  mutable indv_body : mutual_inductive;
}

and mutual_inductive = private {
  mind_hash      : int;
  mind_finite    : recursivity_kind;
  mind_npars     : int;
  mind_npars_rec : int;
  mind_bodies    : one_inductive array;
}

and one_inductive = private {
  oind_hash  : int;
  oind_name  : string;
  oind_type  : typ;
  oind_nargs : int;
  oind_ndecls: int;
  oind_ctors : constructor array;
  oind_projs : (string * term * typ) array;
}

and constructor = private {
  ctor_hash  : int;
  ctor_name  : string;
  ctor_type  : typ;
  ctor_nargs : int;
  ctor_ndecls: int;
}

and projection = private {
  proj_hash  : int;
  proj_indv  : inductive * int;
  proj_name  : string;
  proj_npars : int;
  proj_arg   : int;
}

and case = private {
  case_hash   : int;
  case_ndecls : int array;
  case_nargs  : int array;
  case_indv   : inductive * int;
}


val get_inductive_body : inductive * int -> mutual_inductive * one_inductive

val get_projection_body : projection -> string * term * typ

val extract : Constrexpr.constr_expr -> (term, exn) result

val pp_term : Format.formatter -> term -> unit
