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

type prop = Utils.prop
type set  = Utils.set

type _ kind = KindProp : prop kind | KindSet : set kind

type 'a sort = private {
  sort_hash : int;
  sort_desc : 'a sort_desc;
}

and _ sort_desc =
  | SortProp : prop sort_desc
  | SortBool : set sort_desc
  | SortInt  : set sort_desc
  | SortSymbol : string -> set sort_desc
  | SortArray  : set sort -> set sort_desc
  | SortDatatype : datatype * set sort list -> set sort_desc
  | SortDefn : sortdefn * set sort list -> set sort_desc

and sortdefn = private {
  sdef_hash : int;
  sdef_name : string;
  sdef_prms : string list;
  sdef_desc : set sort;
}

and selector = private {
  slct_hash : int;
  slct_name : string;
  slct_sort : set sort;
}

and constructor = private {
  cnsr_hash : int;
  cnsr_name : string;
  selectors : selector list
}

and datatype = private {
  dttp_hash : int;
  dttp_name : string;
  dttp_prms : string list;
  constructors : constructor list;
}

type var = private {
  var_hash : int;
  var_name : string;
  var_sort : set sort;
}

type (_,_) vrop =
  | Distinct : (set, prop) vrop

type (_,_) unop =
  | Classic : (prop, set) unop
  | Not  : (prop, prop) unop
  | Succ : (set, set) unop

type (_,_,_) bnop =
  | Imply : (prop, prop, prop) bnop
  | And   : (prop, prop, prop) bnop
  | Or    : (prop, prop, prop) bnop
  | Equal : (set, set, prop) bnop
  | Le    : (set, set, prop) bnop
  | Lt    : (set, set, prop) bnop
  | Ge    : (set, set, prop) bnop
  | Gt    : (set, set, prop) bnop
  | Add   : (set, set, set) bnop
  | Sub   : (set, set, set) bnop

and 'a term = private {
  term_hash : int;
  term_sort : 'a sort;
  term_desc : 'a term_desc;
  term_free : var list;
}

and _ term_desc =
  | TermTrue  : prop term_desc
  | TermFalse : prop term_desc
  | TermBool  : bool -> set term_desc
  | TermInt   : int  -> set term_desc

  | TermVar    : var -> set term_desc
  | TermLet    : var * set term * 'a term -> 'a term_desc
  | TermExists : var * prop term -> prop term_desc
  | TermForall : var * prop term -> prop term_desc
  | TermMatch  : set term * 'a case list -> 'a term_desc
  | TermIte    : set term * 'a term * 'a term -> 'a term_desc

  | TermVariadic : ('a,'b) vrop * 'a term list -> 'b term_desc
  | TermUnop : ('a,'b) unop * 'a term -> 'b term_desc
  | TermBnop : ('a,'b,'c) bnop * 'a term * 'b term -> 'c term_desc
  | TermDecl : 'a fundecl * set sort list * set term list -> 'a term_desc
  | TermDefn : 'a fundefn * set sort list * set term list -> 'a term_desc

  | TermConstruct : datatype * set sort list * int * set term list -> set term_desc
  | TermSelect    : datatype * set sort list * int * int * set term -> set term_desc

  | ArrayConst : set sort * set term -> set term_desc
  | ArrayRead  : set sort * set term * set term -> set term_desc
  | ArrayWrite : set sort * set term * set term * set term -> set term_desc
  | ArrayMap   : set fundefn * set sort list * set term list * set term -> set term_desc
  | ArrayDistinct : set sort * set term -> prop term_desc

and 'a case = private {
  case_hash : int;
  case_name : string;
  case_vars : var list;
  case_desc : 'a term;
}

and 'a fundecl = private {
  fdec_hash : int;
  fdec_name : string;
  fdec_prms : string list;
  fdec_vars : set sort list;
  fdec_desc : 'a sort;
}

and 'a fundefn = private {
  fdef_hash : int;
  fdef_name : string;
  fdef_prms : string list;
  fdef_vars : var list;
  fdef_desc : 'a term;
}

type rule = private {
  rule_hash : int;
  rule_name : string;
  rule_rela : string;
  rule_vars : var list;
  rule_desc : prop term;
}

type relation = private {
  rela_hash : int;
  rela_name : string;
  rela_prms : set sort list;
}

type t =
  | Sort      of sortdefn
  | Datatype  of datatype
  | Function  of set fundefn
  | Predicate of prop fundefn
  | Relation  of relation
  | Query     of relation
  | Rule      of rule

val equal : 'a -> 'a -> bool

val kind : 'a sort -> 'a kind

val mk_sort : 'a sort_desc -> 'a sort

val mk_sort_prop     : prop sort
val mk_sort_bool     : set sort
val mk_sort_int      : set sort
val mk_sort_symbol   : string -> set sort
val mk_sort_array    : set sort -> set sort
val mk_sort_datatype : datatype -> set sort list -> set sort
val mk_sort_defn     : sortdefn -> set sort list -> set sort

val mk_variable : string -> set sort -> var

val mk_term : 'a term_desc -> 'a term

val mk_term_true  : prop term
val mk_term_false : prop term
val mk_term_bool  : bool -> set term
val mk_term_int   : int  -> set term

val mk_term_var    : var -> set term
val mk_term_let    : var -> set term -> 'a term -> 'a term
val mk_term_exists : var -> prop term -> prop term
val mk_term_forall : var -> prop term -> prop term
val mk_term_match  : set term -> 'a case list -> 'a term
val mk_term_ite    : set term -> 'a term -> 'a term -> 'a term

val mk_term_variadic : ('a,'b) vrop -> 'a term list -> 'b term
val mk_term_unop : ('a,'b) unop -> 'a term -> 'b term
val mk_term_bnop : ('a,'b,'c) bnop -> 'a term -> 'b term -> 'c term
val mk_term_decl : 'a fundecl -> set sort list -> set term list -> 'a term
val mk_term_defn : 'a fundefn -> set sort list -> set term list -> 'a term

val mk_term_construct : datatype -> set sort list -> int -> set term list -> set term
val mk_term_select    : datatype -> set sort list -> int -> int -> set term -> set term

val mk_array_const : set sort -> set term -> set term
val mk_array_read  : set sort -> set term -> set term -> set term
val mk_array_write : set sort -> set term -> set term -> set term -> set term
val mk_array_map   : set fundefn -> set sort list -> set term list -> set term -> set term
val mk_array_distinct : set sort -> set term -> prop term

val mk_term_distinct : set term list -> prop term

val mk_term_classic : prop term -> set term
val mk_term_not   : prop term -> prop term
val mk_term_succ  : set term -> set term

val mk_term_imply : prop term -> prop term -> prop term
val mk_term_and   : prop term -> prop term -> prop term
val mk_term_or    : prop term -> prop term -> prop term
val mk_term_equal : set term -> set term -> prop term
val mk_term_lt    : set term -> set term -> prop term
val mk_term_le    : set term -> set term -> prop term
val mk_term_gt    : set term -> set term -> prop term
val mk_term_ge    : set term -> set term -> prop term
val mk_term_add   : set term -> set term -> set term
val mk_term_sub   : set term -> set term -> set term

val mk_case : string -> var list -> 'a term -> 'a case

val mk_selector    : string -> set sort -> selector
val mk_constructor : string -> selector list -> constructor
val mk_datatype    : string -> string list -> constructor list -> datatype

val mk_sortdefn : string -> string list -> set sort -> sortdefn
val mk_fundecl  : string -> string list -> set sort list -> 'a sort -> 'a fundecl
val mk_fundefn  : string -> string list -> var  list -> 'a term -> 'a fundefn
val mk_relation : string -> set sort list -> relation
val mk_rule     : string -> string -> var list -> prop term -> rule

