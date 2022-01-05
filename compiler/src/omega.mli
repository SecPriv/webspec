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

type ('a,'b) constant = private {
  cnst_hash : int;
  cnst_ident: ident;
  cnst_type : 'a;
  cnst_body : 'b option;
}

type 'a kind = {
  kind_hash : int;
  kind_desc : 'a kind_desc;
}

and _ kind_desc =
  | KdProp : prop kind_desc
  | KdSet  : set kind_desc
  | KdArrowSort : _ sym * 'a kind -> 'a kind_desc
  | KdArrowTerm : _ var * 'a kind -> 'a kind_desc

and 'a sym = private {
  sym_hash : int;
  sym_name : name;
  sym_kind : 'a kind;
}

and 'a var = private {
  var_hash : int;
  var_name : name;
  var_kind : 'a kind;
  var_sort : 'a sort;
}

and 'a sort = private {
  sort_hash : int;
  sort_kind : 'a kind;
  sort_desc : 'a sort_desc;
}

and _ sort_desc =
  | StTrue        : prop sort_desc
  | StFalse       : prop sort_desc
  | StBool        : set sort_desc
  | StInt         : set sort_desc
  | StFloat       : set sort_desc
  | StArray       : set sort -> set sort_desc

  | StSymbol      : 'a sym * sort_or_term array -> 'a sort_desc
  | StLambdaSort  : _ sym * 'a sort -> 'a sort_desc
  | StLambdaTerm  : _ var * prop sort -> prop sort_desc
  | StApplySort   : 'a   sort * _ sort -> 'a sort_desc
  | StApplyTerm   : prop sort * _ term -> prop sort_desc
  | StProductSort : _ sym * 'a sort -> 'a sort_desc
  | StProductTerm : _ var * 'a sort -> 'a sort_desc

  | StConstant    : ('a kind,'a sort) constant * sort_or_term array -> 'a sort_desc
  | StInductive   : ('a inductive * int)       * sort_or_term array -> 'a sort_desc
  | StPrimitive   : Primitive.relation  * 'a kind * sort_or_term array -> 'a sort_desc
  | StCase        : ('a,prop kind) case * 'a term * prop sort array -> prop sort_desc

and 'a term = private {
  term_hash : int;
  term_kind : 'a kind;
  term_sort : 'a sort;
  term_desc : 'a term_desc;
}

and _ term_desc =
  | TmTrue       : prop term_desc
  | TmBool       : bool  -> set term_desc
  | TmInt        : int   -> set term_desc
  | TmFloat      : float -> set term_desc
  | TmArray      : set term array * set term -> set term_desc

  | TmVariable   : 'a var * sort_or_term array -> 'a term_desc
  | TmLambdaSort : _ sym * 'a term -> 'a term_desc
  | TmLambdaTerm : _ var * 'a term -> 'a term_desc
  | TmApplySort  : 'a term * _ sort -> 'a term_desc
  | TmApplyTerm  : 'a term * _ term -> 'a term_desc

  | TmConstant   : ('a sort,'a term) constant * sort_or_term array -> 'a term_desc
  | TmConstruct  : ('a inductive * int) * int * sort_or_term array -> 'a term_desc
  | TmProject    : ('a,'b) projection * 'a term -> 'b term_desc
  | TmPrimitive  : Primitive.constant * 'a sort * sort_or_term array -> 'a term_desc
  | TmCase       : ('a,'b sort) case  * 'a term  * 'b term array -> 'b term_desc

and sort_or_term = Sort : _ sort -> sort_or_term | Term : _ term -> sort_or_term

(* TODO: Mutual inductive with mixed kind *)
and 'a inductive = private {
  indv_hash  : int;
  indv_ident : ident;
  mutable indv_body : 'a mutual_inductive;
}

and 'a mutual_inductive = private {
  mind_hash   : int;
  mind_npars  : int;
  mind_bodies : 'a one_inductive array;
}

and 'a one_inductive = private {
  oind_hash  : int;
  oind_name  : string;
  oind_kind  : 'a kind;
  oind_ctors : 'a constructor array;
}

and 'a constructor = private {
  ctor_hash : int;
  ctor_name : string;
  ctor_kind : 'a kind;
  ctor_sort : 'a sort;
  ctor_nargs : int;
}

and ('a,'b) projection = private {
  proj_hash : int;
  proj_indv : 'a inductive * int;
  proj_name : string;
  proj_sort : 'b sort;
  proj_indx : int;
}

and ('a,'b) case = private {
  case_hash   : int;
  case_nargs  : int array;
  case_indv   : 'a inductive * int;
  case_type   : 'b;
}

val witness : 'a kind -> 'a witness

val extract_relation : Cic.term -> (prop inductive * int) Result.t
val extract_datatype : Cic.term -> (set  inductive * int) Result.t
val extract_lemma    : Cic.term -> (prop sort,prop term) constant Result.t

val pp_kind : Format.formatter -> _ kind -> unit
val pp_sort : Format.formatter -> _ sort -> unit
val pp_term : Format.formatter -> _ term -> unit

val pp_inductive : Format.formatter -> _ inductive -> unit
