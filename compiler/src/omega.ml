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
open Result.Monad

module Log = Logger.Default
    (struct
      let name = "omega"
    end)

type ('a,'b) constant = {
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

and 'a sym = {
  sym_hash : int;
  sym_name : name;
  sym_kind : 'a kind;
}

and 'a var = {
  var_hash : int;
  var_name : name;
  var_kind : 'a kind;
  var_sort : 'a sort;
}

and 'a sort = {
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

and 'a term = {
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

and sort_or_term =
  | Sort : _ sort -> sort_or_term
  | Term : _ term -> sort_or_term

and 'a inductive = {
  indv_hash  : int;
  indv_ident : ident;
  mutable indv_body : 'a mutual_inductive;
}

and 'a mutual_inductive = {
  mind_hash   : int;
  mind_npars  : int;
  mind_bodies : 'a one_inductive array;
}

and 'a one_inductive = {
  oind_hash  : int;
  oind_name  : string;
  oind_kind  : 'a kind;
  oind_ctors : 'a constructor array;
}

and 'a constructor = {
  ctor_hash : int;
  ctor_name : string;
  ctor_kind : 'a kind;
  ctor_sort : 'a sort;
  ctor_nargs : int;
}

and ('a,'b) projection = {
  proj_hash : int;
  proj_indv : 'a inductive * int;
  proj_name : string;
  proj_sort : 'b sort;
  proj_indx : int;
}

and ('a,'b) case = {
  case_hash   : int;
  case_nargs  : int array;
  case_indv   : 'a inductive * int;
  case_type   : 'b;
}

(******************************************************************************)

let pp_constant :
  type a b. (Format.formatter -> a -> unit) -> (Format.formatter -> b -> unit) ->
  Format.formatter -> (a,b) constant -> unit =
  fun f g fmt { cnst_ident; cnst_type; cnst_body; _ } ->
  Format.fprintf fmt "@[<hov 1>{cnst_name: %a@\ncnst_type: %a@\ncnst_body: %a}@]"
    pp_ident cnst_ident
    f cnst_type
    (Format.pp_print_option g) cnst_body


let rec pp_sym : type a. Format.formatter -> a sym -> unit =
  fun fmt sym ->
  Format.fprintf fmt "@[<hov 1>{sym_name: %a@\nsym_kind: %a}@]"
    Name.pp sym.sym_name
    pp_kind sym.sym_kind

and pp_var : type a. Format.formatter -> a var -> unit =
  fun fmt var ->
  Format.fprintf fmt "@[<hov 1>{var_name: %a@\nvar_kind: %a@\nvar_sort: %a}@]"
    Name.pp var.var_name
    pp_kind var.var_kind
    pp_sort var.var_sort

and pp_kind : type a. Format.formatter -> a kind -> unit =
  fun fmt kind ->
  match kind.kind_desc with
  | KdProp -> Format.fprintf fmt "KdProp"
  | KdSet  -> Format.fprintf fmt "KdSet"
  | KdArrowSort (s, kd) ->
    Format.fprintf fmt "@[<hov 1>(KdArrowSort@ %a@ %a)@]" pp_sym s pp_kind kd
  | KdArrowTerm (v, kd) ->
    Format.fprintf fmt "@[<hov 1>(KdArrowTerm@ %a@ %a)@]" pp_var v pp_kind kd

and pp_sort : type a. Format.formatter -> a sort -> unit =
  fun fmt sort ->
  match sort.sort_desc with
  | StTrue  -> Format.fprintf fmt "StTrue"
  | StFalse -> Format.fprintf fmt "StFalse"
  | StBool  -> Format.fprintf fmt "StBool"
  | StInt   -> Format.fprintf fmt "StInt"
  | StFloat -> Format.fprintf fmt "StFloat"
  | StArray st -> Format.fprintf fmt "@[<hov 1>(StArray@ %a)@]" pp_sort st
  | StSymbol (s, array) ->
    Format.fprintf fmt "@[<hov 1>(StSymbol %a@ [@[%a@]])@]"
      pp_sym s
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StLambdaSort (s, st) -> Format.fprintf fmt "@[<hov 1>(StLambdaSort@ %a@ %a)@]" pp_sym s pp_sort st
  | StLambdaTerm (v, st) -> Format.fprintf fmt "@[<hov 1>(StLambdaTerm@ %a@ %a)@]" pp_var v pp_sort st
  | StApplySort (fn, st) -> Format.fprintf fmt "@[<hov 1>(StApplySort@ %a@ %a)@]" pp_sort fn pp_sort st
  | StApplyTerm (fn, tm) -> Format.fprintf fmt "@[<hov 1>(StApplyTerm@ %a@ %a)@]" pp_sort fn pp_term tm
  | StProductSort (s, st) -> Format.fprintf fmt "@[<hov 1>(StProductSort@ %a@ %a)@]" pp_sym s pp_sort st
  | StProductTerm (v, st) -> Format.fprintf fmt "@[<hov 1>(StProductTerm@ %a@ %a)@]" pp_var v pp_sort st
  | StConstant (cn, array) ->
    Format.fprintf fmt "@[<hov 1>(StConstant@ %a@ [@[%a@]])@]"
      (pp_constant pp_kind pp_sort) cn
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StInductive ((iv,int), array) ->
    let oind = iv.indv_body.mind_bodies.(int) in
    Format.fprintf fmt "@[<hov 1>(StInductive %s:@ %a@ [@[%a@]])@]"
      oind.oind_name
      pp_kind oind.oind_kind
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StPrimitive (pm, kd, array) ->
    Format.fprintf fmt "@[<hov 1>(StPrimitive %s:@ %a@ [@[%a@]]@])"
      (Primitive.relation_to_string pm)
      pp_kind kd
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StCase (cs, tm, array) ->
    Format.fprintf fmt "@[<hov 1>(StCase@ [%a]@ %a@ [@[%a@]])@]"
      (Format.pp_print_list Format.pp_print_int) (Array.to_list cs.case_nargs)
      pp_term tm
      (Format.pp_print_list pp_sort) (Array.to_list array)

and pp_term : type a. Format.formatter -> a term -> unit =
  fun fmt term ->
  match term.term_desc with
  | TmTrue -> Format.fprintf fmt "TmTrue"
  | TmBool bool -> Format.fprintf fmt "@[<hov 1>(TmBool %s)@]" (string_of_bool bool)
  | TmInt  int  -> Format.fprintf fmt "@[<hov 1>(TmInt %i)@]" int
  | TmFloat float -> Format.fprintf fmt "@[<hov 1>(TmFloat %f)@]" float
  | TmArray (array, tm) ->
    Format.fprintf fmt "@[<hov 1>(TmArray@ [@[%a@]]@ %a)@]"
      (Format.pp_print_list pp_term) (Array.to_list array)
      pp_term tm
  | TmVariable (v, array) ->
    Format.fprintf fmt "@[<hov 1>(TmVariable %a@ [@[%a@]])@]"
      pp_var v
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | TmLambdaSort (s, tm) -> Format.fprintf fmt "@[<hov 1>(TmLambdaSort@ %a@ %a)@]" pp_sym s pp_term tm
  | TmLambdaTerm (v, tm) -> Format.fprintf fmt "@[<hov 1>(TmLambdaTerm@ %a@ %a)@]" pp_var v pp_term tm
  | TmApplySort (fn, st) -> Format.fprintf fmt "@[<hov 1>(TmApplySort@ %a@ %a)@]" pp_term fn pp_sort st
  | TmApplyTerm (fn, tm) -> Format.fprintf fmt "@[<hov 1>(TmApplyTerm@ %a@ %a)@]" pp_term fn pp_term tm
  | TmConstant (cn, array) ->
    Format.fprintf fmt "@[<hov 1>(TmConstant@ %a@ [@[%a@]])@]"
      (pp_constant pp_sort pp_term) cn
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | TmConstruct ((iv,int1), int2, array) ->
    let ctor = iv.indv_body.mind_bodies.(int1).oind_ctors.(int2) in
    Format.fprintf fmt "@[<hov 1>(TmConstruct %s:@ %a@ [@[%a@]])@]"
      ctor.ctor_name
      pp_sort ctor.ctor_sort
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | TmProject (pj, tm) ->
    Format.fprintf fmt "@[<hov 1>(TmProject %s:@ %a@ %a)@]"
      pj.proj_name
      pp_sort pj.proj_sort
      pp_term tm
  | TmPrimitive (pm, st, array) ->
    Format.fprintf fmt "@[<hov 1>(StPrimitive %s:@ %a@ [@[%a@]]@])"
      (Primitive.constant_to_string pm)
      pp_sort st
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | TmCase (cs, tm, array) ->
    Format.fprintf fmt "@[<hov 1>(TmCase@ [%a]@ %a@ [@[%a@]])@]"
      (Format.pp_print_list Format.pp_print_int) (Array.to_list cs.case_nargs)
      pp_term tm
      (Format.pp_print_list pp_term) (Array.to_list array)

and pp_sort_or_term : Format.formatter -> sort_or_term -> unit =
  fun fmt sort_or_term ->
  match sort_or_term with
  | Sort sort -> Format.fprintf fmt "@[<hov 1>(Sort@ %a)@]" pp_sort sort
  | Term term -> Format.fprintf fmt "@[<hov 1>(Term@ %a)@]" pp_term term


let pp_constructor : type a. Format.formatter -> a constructor -> unit =
  fun fmt { ctor_name; ctor_kind; ctor_sort; ctor_nargs; _ } ->
  Format.fprintf fmt "@[<hov 1>{ctor_name: %s@\nctor_nargs: %i@\nctor_kind:@ %a@\nctor_sort:@ %a}@]"
    ctor_name ctor_nargs
    pp_kind ctor_kind
    pp_sort ctor_sort

let pp_one_inductive : type a. Format.formatter -> a one_inductive -> unit =
  fun fmt { oind_name; oind_kind; oind_ctors; _ } ->
  Format.fprintf fmt "@[<hov 1>{oind_name: %s@\noind_kind:@ %a@\noind_ctors:@ [@[%a@]]}@]"
    oind_name
    pp_kind oind_kind
    (Format.pp_print_list pp_constructor) (Array.to_list oind_ctors)

let pp_mutual_inductive : type a. Format.formatter -> a mutual_inductive -> unit =
  fun fmt { mind_npars; mind_bodies; _ } ->
  Format.fprintf fmt "@[<hov 1>{mind_npars: %i@\nmind_bodies:@ [@[%a@]]}@]"
    mind_npars
    (Format.pp_print_list pp_one_inductive) (Array.to_list mind_bodies)

let pp_inductive : type a. Format.formatter -> a inductive -> unit =
  fun fmt { indv_ident; indv_body; _ } ->
  Format.fprintf fmt "@[<hov 1>{indv_ident: %a@\nindv_body:@ %a}@]"
    pp_ident indv_ident
    pp_mutual_inductive indv_body

(******************************************************************************)

type sym_or_var = Sym : _ sym -> sym_or_var | Var : _ var -> sym_or_var

let rec get_arrows : type a. int -> sym_or_var list -> a kind -> a kind * sym_or_var array =
  fun n acc kind ->
  if n > 0 then
    match kind.kind_desc with
    | KdProp -> kind, Array.of_list (List.rev acc)
    | KdSet  -> kind, Array.of_list (List.rev acc)
    | KdArrowSort (s, kd) -> get_arrows (n-1) (Sym s :: acc) kd
    | KdArrowTerm (v, kd) -> get_arrows (n-1) (Var v :: acc) kd
  else
    kind, Array.of_list (List.rev acc)

let get_arrows ?(n=max_int) kind = get_arrows n [] kind


let rec get_products : type a. int -> sym_or_var list -> a sort -> a sort * sym_or_var array =
  fun n acc sort ->
  if n  > 0 then
    match sort.sort_desc with
    | StProductSort (s, st) -> get_products (n-1) (Sym s :: acc) st
    | StProductTerm (v, st) -> get_products (n-1) (Var v :: acc) st
    | _ -> sort, Array.of_list (List.rev acc)
  else sort, Array.of_list (List.rev acc)

let get_products ?(n=max_int) sort = get_products n [] sort


let rec equal_kind : type a b. a kind -> b kind -> (a,b) eq =
  fun kd1 kd2 ->
  match kd1.kind_desc, kd2.kind_desc with
  | KdProp, KdProp -> Eq
  | KdSet,  KdSet  -> Eq
  | KdArrowSort (s1, kd1), KdArrowSort (s2, kd2) ->
    (match equal_kind s1.sym_kind s2.sym_kind, equal_kind kd1 kd2 with
     | Eq, Eq -> Eq
     | _, _ -> Nq)
  | KdArrowTerm (v1, kd1), KdArrowTerm (v2, kd2) ->
    (match equal_kind v1.var_kind v2.var_kind, equal_kind kd1 kd2 with
     | Eq, Eq -> Eq
     | _, _ -> Nq)
  | _, _ -> Nq

let rec witness : type a. a kind -> a witness =
  fun kd ->
  match kd.kind_desc with
  | KdProp -> Prop
  | KdSet  -> Set
  | KdArrowSort (_, kd) -> witness kd
  | KdArrowTerm (_, kd) -> witness kd

let _ensure : type a b. ('c * ('c -> a witness)) -> ('d * ('d -> b witness)) -> (a,b) eq =
  fun (x, f) (y, g) -> equal_witness (f x) (g y)

type any_sym = AnySym : _ sym -> any_sym
type any_var = AnyVar : _ var -> any_var

type any_kind = AnyKind : _ kind -> any_kind
type any_sort = AnySort : _ sort -> any_sort
type any_term = AnyTerm : _ term -> any_term

type any_inductive = AnyInductive : _ inductive -> any_inductive
type any_mutual_inductive = AnyMutualInductive : _ mutual_inductive -> any_mutual_inductive
type any_one_inductive = AnyOneInductive : _ one_inductive -> any_one_inductive
type any_constructor = AnyConstructor : _ constructor -> any_constructor
type any_projection = AnyProjection : (_,_) projection -> any_projection
type _ any_case = AnyCase : (_, 'b) case -> 'b any_case

let unpack_kind :
  type a. a witness -> any_kind -> a kind Result.t =
  fun wt (AnyKind kind) ->
  match equal_witness wt (witness kind) with
  | Eq -> Ok kind
  | Nq -> failure (fun _ -> "Omega.unpack_kind")

let unpack_sort :
  type a. a witness -> any_sort -> a sort Result.t =
  fun wt (AnySort sort) ->
  match equal_witness wt (witness sort.sort_kind) with
  | Eq -> Ok sort
  | Nq -> failure (fun _ -> "Omega.unpack_sort")

let unpack_term :
  type a. a witness -> any_term -> a term Result.t =
  fun wt (AnyTerm term) ->
  match equal_witness wt (witness term.term_kind) with
  | Eq -> Ok term
  | Nq -> failure (fun _ -> "Omega.unpack_term")

let unpack_mutual_inductive :
  type a. a witness -> int -> any_mutual_inductive -> a mutual_inductive Result.t =
  fun wt int (AnyMutualInductive mind) ->
  match equal_witness wt (witness mind.mind_bodies.(int).oind_kind) with
  | Eq -> Ok mind
  | Nq -> failure (fun _ -> "Omega.unpack_mutual_inductive")

let unpack_one_inductive :
  type a. a witness -> any_one_inductive -> a one_inductive Result.t =
  fun wt (AnyOneInductive oind) ->
  match equal_witness wt (witness oind.oind_kind) with
  | Eq -> Ok oind
  | Nq -> failure (fun _ -> "Omega.unpack_one_inductive")

let unpack_constructor :
  type a. a witness -> any_constructor -> a constructor Result.t =
  fun wt (AnyConstructor ctor) ->
  match equal_witness wt (witness ctor.ctor_kind) with
  | Eq -> Ok ctor
  | Nq -> failure (fun _ -> "Omega.unpack_constructor")


type env = {
  cic_map : Cic.term NameMap.t;
  sym_map : any_sym NameMap.t;
  var_map : any_var NameMap.t;
  ind_map : any_inductive StringHashtbl.t;
}

let create n = {
  cic_map = NameMap.empty;
  sym_map = NameMap.empty;
  var_map = NameMap.empty;
  ind_map = StringHashtbl.create n;
}

let add_cic nm t env =
  { env with cic_map = NameMap.add nm t env.cic_map }

let add_sym sym env =
  { env with sym_map = NameMap.add sym.sym_name (AnySym sym) env.sym_map }

let add_var var env =
  { env with var_map = NameMap.add var.var_name (AnyVar var) env.var_map }

let add_ind ind env =
  let string = ident_to_string ind.indv_ident in
  assert (not (StringHashtbl.mem env.ind_map string));
  StringHashtbl.add env.ind_map string (AnyInductive ind);
  env

let find_cic name env = NameMap.find_opt name env.cic_map
let find_sym name env = NameMap.find_opt name env.sym_map
let find_var name env = NameMap.find_opt name env.var_map
let find_ind string env = StringHashtbl.find_opt env.ind_map string

type subst = {
  ind_subst : any_inductive StringMap.t;
}

let empty = { ind_subst = StringMap.empty }
(*
let add_ind_subst ind subst =
  let string = ident_to_string ind.indv_ident in
  { ind_subst = StringMap.add string (AnyInductive ind) subst.ind_subst }

let find_ind_subst string subst = StringMap.find_opt string subst.ind_subst
*)
(******************************************************************************)

(*
let hash_any_syms array = Array.map (function AnySym s -> s.sym_hash) array
let hash_any_vars array = Array.map (function AnyVar v -> v.var_hash) array

let hash_any_sorts array = Array.map (function AnySort st -> st.sort_hash) array
let hash_any_terms array = Array.map (function AnyTerm tm -> tm.term_hash) array
*)

let mk_constant cnst_ident cnst_type cnst_body =
  let cnst_hash = Hashtbl.hash cnst_ident in
  { cnst_hash; cnst_ident; cnst_type; cnst_body }

let mk_symbol sym_name sym_kind =
  let sym_hash = Hashtbl.hash (sym_name, sym_kind.kind_hash) in
  { sym_hash; sym_name; sym_kind }

let mk_variable var_name var_kind var_sort =
  let var_hash = Hashtbl.hash (var_name, var_kind.kind_hash, var_sort.sort_hash) in
  { var_hash; var_name; var_kind; var_sort }

let mk_kind : type a. a kind_desc -> a kind =
  fun kind_desc ->
  let kind_hash =
    match kind_desc with
    | KdProp -> Hashtbl.hash "KdProp"
    | KdSet -> Hashtbl.hash "KdSet"
    | KdArrowSort (s, kd) -> Hashtbl.hash ("KdArrowSort", s.sym_hash, kd.kind_hash)
    | KdArrowTerm (v, kd) -> Hashtbl.hash ("KdArrowTerm", v.var_hash, kd.kind_hash)
  in
  { kind_hash; kind_desc }

let is_ground : type a. a kind -> bool =
  fun kind ->
  match kind.kind_desc with
  | KdProp -> true
  | KdSet  -> true
  | KdArrowSort (_,_) -> false
  | KdArrowTerm (_,_) -> false

let mk_kind_prop = mk_kind KdProp
let mk_kind_set  = mk_kind KdSet
let mk_kind_arrow_sort s kd = mk_kind (KdArrowSort (s, kd))
let mk_kind_arrow_term v kd = mk_kind (KdArrowTerm (v, kd))

let mk_inductive indv_ident indv_body =
  let indv_hash =
    Hashtbl.hash (indv_ident, indv_body.mind_hash)
  in
  { indv_hash; indv_ident; indv_body }

let mk_mutual_inductive mind_npars mind_bodies =
  let mind_hash =
    Hashtbl.hash (mind_npars, Array.map (fun oind -> oind.oind_hash) mind_bodies)
  in
  { mind_hash; mind_npars; mind_bodies }

let mk_one_inductive oind_name oind_kind oind_ctors =
  let oind_hash =
    Hashtbl.hash (oind_name, oind_kind.kind_hash,
                  Array.map (fun ctor -> ctor.ctor_hash) oind_ctors)
  in
  { oind_hash; oind_name; oind_kind; oind_ctors }

let mk_constructor ctor_name ctor_kind ctor_sort ctor_nargs =
  let ctor_hash =
    Hashtbl.hash (ctor_name, ctor_kind.kind_hash, ctor_sort.sort_hash, ctor_nargs)
  in
  { ctor_hash; ctor_name; ctor_kind; ctor_sort; ctor_nargs }

let mk_projection (indv,int as proj_indv) proj_name proj_sort proj_indx =
  let proj_hash =
    Hashtbl.hash (indv.indv_hash, int, proj_name, proj_sort.sort_hash, proj_indx)
  in
  { proj_hash; proj_indv; proj_name; proj_sort; proj_indx }

let mk_case (indv,int as case_indv) case_type case_nargs =
  let case_hash =
    Hashtbl.hash (indv.indv_hash, int, case_nargs)
  in
  { case_hash; case_nargs; case_indv; case_type }


let term_kind_of_sort : type a. a sort -> a kind =
  let rec aux : type a. a kind -> a kind =
    fun kind ->
      match kind.kind_desc with
      | KdProp -> mk_kind_prop
      | KdSet -> mk_kind_set
      | KdArrowSort (_, kd) -> aux kd
      | KdArrowTerm (_, kd) -> aux kd
  in
  let rec term_kind_of_sort : type a. a sort -> a kind =
    fun sort ->
      match sort.sort_desc with
      | StTrue -> mk_kind_prop
      | StFalse -> mk_kind_prop
      | StBool -> mk_kind_set
      | StInt -> mk_kind_set
      | StFloat -> mk_kind_set
      | StArray _ -> mk_kind_set
      | StSymbol (s, _) -> aux s.sym_kind
      | StLambdaSort (_, st) -> term_kind_of_sort st
      | StLambdaTerm (_, st) -> term_kind_of_sort st
      | StApplySort (st, _) -> term_kind_of_sort st
      | StApplyTerm (st, _) -> term_kind_of_sort st
      | StProductSort (s, st) -> mk_kind_arrow_sort s (term_kind_of_sort st)
      | StProductTerm (v, st) -> mk_kind_arrow_term v (term_kind_of_sort st)
      | StConstant (cn, _) ->
        (match cn.cnst_body with
         | None -> aux cn.cnst_type
         | Some st -> term_kind_of_sort st)
      | StInductive ((iv, int), _) -> aux iv.indv_body.mind_bodies.(int).oind_kind
      | StPrimitive (_,kd,_) -> aux kd
      | StCase (cs, _, _) -> aux cs.case_type
  in
  fun sort ->
    assert (is_ground sort.sort_kind);
    term_kind_of_sort sort


let hash_sort_or_term_array array =
  Array.map (function Sort s -> s.sort_hash | Term t -> t.term_hash) array


let subst_symbol :
  type a. (subst -> a kind -> a kind) -> subst -> a sym -> a sym =
  fun subst env sym ->
  mk_symbol sym.sym_name (subst env sym.sym_kind)


let subst_variable :
  type a. (subst -> a kind -> a kind) -> (subst -> a sort -> a sort) -> subst -> a var -> a var =
  fun subst_kind subst_sort env var ->
  mk_variable var.var_name (subst_kind env var.var_kind) (subst_sort env var.var_sort)

(*
let subst_inductive :
  type a. (subst -> a kind -> a kind) -> (subst -> a sort -> a sort) -> subst ->
  a inductive * int -> a inductive * int =
  fun subst_kind subst_sort env (indv, int) ->
  let string = ident_to_string indv.indv_ident in
  match find_ind_subst string env with
  | Some (AnyInductive indv') ->
    (match
       equal_kind
         indv.indv_body.mind_bodies.(int).oind_kind
         indv'.indv_body.mind_bodies.(int).oind_kind
     with
     | Eq -> indv', int
     | Nq -> assert false)
  | None ->
    let indv = mk_inductive indv.indv_ident indv.indv_body in
    let env = add_ind_subst indv env in
    let indv_body =
      mk_mutual_inductive indv.indv_body.mind_npars
        (Array.map
           (fun { oind_name; oind_kind; oind_ctors; _ } ->
              mk_one_inductive oind_name (subst_kind env oind_kind)
                (Array.map
                   (fun { ctor_name; ctor_kind; ctor_sort; ctor_nargs; _ } ->
                      mk_constructor ctor_name
                        (subst_kind env ctor_kind)
                        (subst_sort env ctor_sort)
                        ctor_nargs)
                   oind_ctors))
           indv.indv_body.mind_bodies)
    in
    indv.indv_body <- indv_body;
    indv, int
*)

let rec subst_sym_kind : type a b. a sym -> a sort -> subst -> b kind -> b kind =
  fun s' st' env kind ->
  match kind.kind_desc with
  | KdProp -> kind
  | KdSet  -> kind
  | KdArrowSort (s, kd) ->
    let s = subst_symbol (subst_sym_kind s' st') env s in
    let kd = subst_sym_kind s' st' env kd in
    mk_kind_arrow_sort s kd
  | KdArrowTerm (v, kd) ->
    let v = subst_variable (subst_sym_kind s' st') (subst_sym_sort s' st') env v in
    let kd = subst_sym_kind s' st' env kd in
    mk_kind_arrow_term v kd


and subst_sym_sort : type a b. a sym -> a sort -> subst -> b sort -> b sort =
  fun s' st' env sort ->
  match sort.sort_desc with
  | StTrue  -> sort
  | StFalse -> sort
  | StBool  -> sort
  | StInt   -> sort
  | StFloat -> sort
  | StArray st -> mk_sort (StArray (subst_sym_sort s' st' env st))
  | StSymbol (s, array) ->
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    if Name.equal s.sym_name s'.sym_name then
      match equal_kind s.sym_kind s'.sym_kind with
      | Eq -> Array.fold_left sort_apply_sort_or_term st' array
      | Nq -> assert false
    else
      let s = subst_symbol (subst_sym_kind s' st') env s in
      mk_sort (StSymbol (s, array))
  | StLambdaSort (s, st) ->
    let s = subst_symbol (subst_sym_kind s' st') env s in
    if Name.equal s.sym_name s'.sym_name then mk_sort (StLambdaSort (s, st))
    else mk_sort (StLambdaSort (s, subst_sym_sort s' st' env st))
  | StLambdaTerm (v, st) ->
    let v = subst_variable (subst_sym_kind s' st') (subst_sym_sort s' st') env v in
    mk_sort (StLambdaTerm (v, subst_sym_sort s' st' env st))
  | StApplySort (fn, st) ->
    let fn = subst_sym_sort s' st' env fn in
    let st = subst_sym_sort s' st' env st in
    mk_sort (StApplySort (fn, st))
  | StApplyTerm (fn, tm) ->
    let fn = subst_sym_sort s' st' env fn in
    let tm = subst_sym_term s' st' env tm in
    mk_sort (StApplyTerm (fn, tm))
  | StProductSort (s, st) ->
    let s = subst_symbol (subst_sym_kind s' st') env s in
    if Name.equal s.sym_name s'.sym_name then mk_sort (StProductSort (s, st))
    else mk_sort (StProductSort (s, subst_sym_sort s' st' env st))
  | StProductTerm (v, st) ->
    let v = subst_variable (subst_sym_kind s' st') (subst_sym_sort s' st') env v in
    mk_sort (StProductTerm (v, subst_sym_sort s' st' env st))
  | StConstant (cn, array) ->
    (*let cnst_type = subst_sym_kind s' st' env cnst_type in
      let cnst_body = Option.map (subst_sym_sort s' st' env) cnst_body in*)
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_sort (StConstant ((*mk_constant cnst_name cnst_type cnst_body*)cn, array))
  | StInductive (iv, array) ->
    (*let iv = subst_inductive (subst_sym_kind s' st') (subst_sym_sort s' st') env iv in*)
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_sort (StInductive (iv, array))
  | StPrimitive (pm, kd, array) ->
    let kd = subst_sym_kind s' st' env kd in
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_sort (StPrimitive (pm, kd, array))
  | StCase ({ case_nargs; case_indv; case_type; _ }, tm, array) ->
    let cs =
      mk_case
        case_indv(*(subst_inductive (subst_sym_kind s' st') (subst_sym_sort s' st') env case_indv)*)
        (subst_sym_kind s' st' env case_type)
        case_nargs
    in
    let tm = subst_sym_term s' st' env tm in
    let array = Array.map (subst_sym_sort s' st' env) array in
    mk_sort (StCase (cs, tm, array))


and subst_sym_term : type a b. a sym -> a sort -> subst -> b term -> b term =
  fun s' st' env term ->
  match term.term_desc with
  | TmTrue -> term
  | TmBool _ -> term
  | TmInt  _ -> term
  | TmFloat _ -> term
  | TmArray (array, tm) ->
    let array = Array.map (subst_sym_term s' st' env) array in
    let tm = subst_sym_term s' st' env tm in
    mk_term (TmArray (array, tm))
  | TmVariable (v, array) ->
    let v = subst_variable (subst_sym_kind s' st') (subst_sym_sort s' st') env v in
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_term (TmVariable (v, array))
  | TmLambdaSort (s, tm) ->
    let s = subst_symbol (subst_sym_kind s' st') env s in
    if Name.equal s.sym_name s'.sym_name then mk_term (TmLambdaSort (s, tm))
    else mk_term (TmLambdaSort (s, subst_sym_term s' st' env tm))
  | TmLambdaTerm (v, tm) ->
    let v = subst_variable (subst_sym_kind s' st') (subst_sym_sort s' st') env v in
    mk_term (TmLambdaTerm (v, subst_sym_term s' st' env tm))
  | TmApplySort (fn, st) ->
    let fn = subst_sym_term s' st' env fn in
    let st = subst_sym_sort s' st' env st in
    mk_term (TmApplySort (fn, st))
  | TmApplyTerm (fn, tm) ->
    let fn = subst_sym_term s' st' env fn in
    let tm = subst_sym_term s' st' env tm in
    mk_term (TmApplyTerm (fn, tm))
  | TmConstant (cn, array) ->
    (*let cnst_type = subst_sym_sort s' st' env cnst_type in
      let cnst_body = Option.map (subst_sym_term s' st' env) cnst_body in*)
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_term (TmConstant ((*mk_constant cnst_name cnst_type cnst_body*)cn, array))
  | TmConstruct (iv, int, array) ->
    (*let iv = subst_inductive (subst_sym_kind s' st') (subst_sym_sort s' st') env iv in*)
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_term (TmConstruct (iv, int, array))
  | TmProject ({ proj_indv; proj_name; proj_sort; proj_indx; _ }, tm) ->
    let pj =
      mk_projection
        proj_indv(*(subst_inductive (subst_sym_kind s' st') (subst_sym_sort s' st') env proj_indv)*)
        proj_name
        (subst_sym_sort s' st' env proj_sort)
        proj_indx
    in
    mk_term (TmProject (pj, subst_sym_term s' st' env tm))
  | TmPrimitive (pm, st, array) ->
    let st = subst_sym_sort s' st' env st in
    let array = Array.map (subst_sym_sort_or_term s' st' env) array in
    mk_term (TmPrimitive (pm, st, array))
  | TmCase ({ case_nargs; case_indv; case_type; _ }, tm, array) ->
    let cs =
      mk_case
        case_indv(*(subst_inductive (subst_sym_kind s' st') (subst_sym_sort s' st') env case_indv)*)
        (subst_sym_sort s' st' env case_type)
        case_nargs
    in
    let tm = subst_sym_term s' st' env tm in
    let array = Array.map (subst_sym_term s' st' env) array in
    mk_term (TmCase (cs, tm, array))


and subst_sym_sort_or_term : type a. a sym -> a sort -> subst -> sort_or_term -> sort_or_term =
  fun s' st' env sort_or_term ->
  match sort_or_term with
  | Sort sort -> Sort (subst_sym_sort s' st' env sort)
  | Term term -> Term (subst_sym_term s' st' env term)


and sort_apply_sort_or_term : type a. a sort -> sort_or_term -> a sort =
  fun sort sort_or_term ->
  match witness sort.sort_kind with
  | Prop ->
    (match sort_or_term with
     | Sort st -> mk_sort (StApplySort (sort, st))
     | Term tm -> mk_sort (StApplyTerm (sort, tm)))
  | Set ->
    (match sort_or_term with
     | Sort st -> mk_sort (StApplySort (sort, st))
     | Term _  -> assert false)


and subst_var_kind : type a b. a var -> a term -> subst -> b kind -> b kind =
  fun v' tm' env kind ->
  match kind.kind_desc with
  | KdProp -> kind
  | KdSet  -> kind
  | KdArrowSort (s, kd) ->
    let s = subst_symbol (subst_var_kind v' tm') env s in
    let kd = subst_var_kind v' tm' env kd in
    mk_kind_arrow_sort s kd
  | KdArrowTerm (v, kd) ->
    let v = subst_variable (subst_var_kind v' tm') (subst_var_sort v' tm') env v in
    let kd = subst_var_kind v' tm' env kd in
    mk_kind_arrow_term v kd


and subst_var_sort : type a b. a var -> a term -> subst -> b sort -> b sort =
  fun v' tm' env sort ->
  match sort.sort_desc with
  | StTrue  -> sort
  | StFalse -> sort
  | StBool  -> sort
  | StInt   -> sort
  | StFloat -> sort
  | StArray st -> mk_sort (StArray (subst_var_sort v' tm' env st))
  | StSymbol (s, array) ->
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_sort (StSymbol (subst_symbol (subst_var_kind v' tm') env s, array))
  | StLambdaSort (s, st) ->
    let s = subst_symbol (subst_var_kind v' tm') env s in
    mk_sort (StLambdaSort (s, subst_var_sort v' tm' env st))
  | StLambdaTerm (v, st) ->
    let v = subst_variable (subst_var_kind v' tm') (subst_var_sort v' tm') env v in
    if Name.equal v.var_name v'.var_name then mk_sort (StLambdaTerm (v, st))
    else mk_sort (StLambdaTerm (v, subst_var_sort v' tm' env st))
  | StApplySort (fn, st) ->
    let fn = subst_var_sort v' tm' env fn in
    let st = subst_var_sort v' tm' env st in
    mk_sort (StApplySort (fn, st))
  | StApplyTerm (fn, tm) ->
    let fn = subst_var_sort v' tm' env fn in
    let tm = subst_var_term v' tm' env tm in
    mk_sort (StApplyTerm (fn, tm))
  | StProductSort (s, st) ->
    let s = subst_symbol (subst_var_kind v' tm') env s in
    mk_sort (StProductSort (s, subst_var_sort v' tm' env st))
  | StProductTerm (v, st) ->
    let v = subst_variable (subst_var_kind v' tm') (subst_var_sort v' tm') env v in
    if Name.equal v.var_name v'.var_name then mk_sort (StProductTerm (v, st))
    else mk_sort (StProductTerm (v, subst_var_sort v' tm' env st))
  | StConstant (cn, array) ->
    (*let cnst_type = subst_var_kind v' tm' env cnst_type in
      let cnst_body = Option.map (subst_var_sort v' tm' env) cnst_body in*)
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_sort (StConstant ((*mk_constant cnst_name cnst_type cnst_body*)cn, array))
  | StInductive (iv, array) ->
    (*let iv = subst_inductive (subst_var_kind v' tm') (subst_var_sort v' tm') env iv in*)
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_sort (StInductive (iv, array))
  | StPrimitive (pm, kd, array) ->
    let kd = subst_var_kind v' tm' env kd in
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_sort (StPrimitive (pm, kd, array))
  | StCase ({ case_nargs; case_indv; case_type; _ }, tm, array) ->
    let cs =
      mk_case
        case_indv(*(subst_inductive (subst_var_kind v' tm') (subst_var_sort v' tm') env case_indv)*)
        (subst_var_kind v' tm' env case_type)
        case_nargs
    in
    let tm = subst_var_term v' tm' env tm in
    let array = Array.map (subst_var_sort v' tm' env) array in
    mk_sort (StCase (cs, tm, array))


and subst_var_term : type a b. a var -> a term -> subst -> b term -> b term =
  fun v' tm' env term ->
  match term.term_desc with
  | TmTrue -> term
  | TmBool _ -> term
  | TmInt  _ -> term
  | TmFloat _ -> term
  | TmArray (array, tm) ->
    let array = Array.map (subst_var_term v' tm' env) array in
    let tm = subst_var_term v' tm' env tm in
    mk_term (TmArray (array, tm))
  | TmVariable (v, array) ->
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    if Name.equal v.var_name v'.var_name then
      match equal_kind v.var_kind v'.var_kind with
      | Eq -> Array.fold_left term_apply_sort_or_term tm' array
      | Nq -> assert false
    else
      let v = subst_variable (subst_var_kind v' tm') (subst_var_sort v' tm') env v in
      mk_term (TmVariable (v, array))
  | TmLambdaSort (s, tm) ->
    let s = subst_symbol (subst_var_kind v' tm') env s in
    mk_term (TmLambdaSort (s, subst_var_term v' tm' env tm))
  | TmLambdaTerm (v, tm) ->
    let v = subst_variable (subst_var_kind v' tm') (subst_var_sort v' tm') env v in
    if Name.equal v.var_name v'.var_name then mk_term (TmLambdaTerm (v, tm))
    else mk_term (TmLambdaTerm (v, subst_var_term v' tm' env tm))
  | TmApplySort (fn, st) ->
    let fn = subst_var_term v' tm' env fn in
    let st = subst_var_sort v' tm' env st in
    mk_term (TmApplySort (fn, st))
  | TmApplyTerm (fn, tm) ->
    let fn = subst_var_term v' tm' env fn in
    let tm = subst_var_term v' tm' env tm in
    mk_term (TmApplyTerm (fn, tm))
  | TmConstant (cn, array) ->
    (*let cnst_type = subst_var_sort v' tm' env cnst_type in
      let cnst_body = Option.map (subst_var_term v' tm' env) cnst_body in*)
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_term (TmConstant ((*mk_constant cnst_name cnst_type cnst_body*)cn, array))
  | TmConstruct (iv, int, array) ->
    (*let iv = subst_inductive (subst_var_kind v' tm') (subst_var_sort v' tm') env iv in*)
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_term (TmConstruct (iv, int, array))
  | TmProject ({ proj_indv; proj_name; proj_sort; proj_indx; _ }, tm) ->
    let pj =
      mk_projection
        proj_indv(*(subst_inductive (subst_var_kind v' tm') (subst_var_sort v' tm') env proj_indv)*)
        proj_name
        (subst_var_sort v' tm' env proj_sort)
        proj_indx
    in
    mk_term (TmProject (pj, subst_var_term v' tm' env tm))
  | TmPrimitive (pm, st, array) ->
    let st = subst_var_sort v' tm' env st in
    let array = Array.map (subst_var_sort_or_term v' tm' env) array in
    mk_term (TmPrimitive (pm, st, array))
  | TmCase ({ case_nargs; case_indv; case_type; _ }, tm, array) ->
    let cs =
      mk_case
        case_indv(*(subst_inductive (subst_var_kind v' tm') (subst_var_sort v' tm') env case_indv)*)
        (subst_var_sort v' tm' env case_type)
        case_nargs
    in
    let tm = subst_var_term v' tm' env tm in
    let array = Array.map (subst_var_term v' tm' env) array in
    mk_term (TmCase (cs, tm, array))


and subst_var_sort_or_term : type a. a var -> a term -> subst -> sort_or_term -> sort_or_term =
  fun v' tm' env sort_or_term ->
  match sort_or_term with
  | Sort sort -> Sort (subst_var_sort v' tm' env sort)
  | Term term -> Term (subst_var_term v' tm' env term)


and term_apply_sort_or_term : type a. a term -> sort_or_term -> a term =
  fun term sort_or_term ->
  match sort_or_term with
  | Sort st -> mk_term (TmApplySort (term, st))
  | Term tm -> mk_term (TmApplyTerm (term, tm))


and sort_hash_kind : type a. a sort_desc -> int * a kind =
  fun sort_desc ->
  match sort_desc with
  | StTrue  -> Hashtbl.hash "StTrue",  mk_kind_prop
  | StFalse -> Hashtbl.hash "StFalse", mk_kind_prop
  | StBool  -> Hashtbl.hash "StBool",  mk_kind_set
  | StInt   -> Hashtbl.hash "StInt",   mk_kind_set
  | StFloat -> Hashtbl.hash "StFloat", mk_kind_set
  | StArray st -> Hashtbl.hash ("StArray", st.sort_hash), mk_kind_set
  | StSymbol (s, array) ->
    Hashtbl.hash ("StSymbol", s.sym_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n:(Array.length array) s.sym_kind)
  | StLambdaSort (s, st) ->
    Hashtbl.hash ("StLambdaSort", s.sym_hash, st.sort_hash),
    mk_kind_arrow_sort s st.sort_kind
  | StLambdaTerm (v, st) ->
    Hashtbl.hash ("StLambdaTerm", v.var_hash, st.sort_hash),
    mk_kind_arrow_term v st.sort_kind
  | StApplySort (st, st') ->
    Hashtbl.hash ("StApplySort", st.sort_hash, st'.sort_hash),
    (match st.sort_kind.kind_desc with
     | KdArrowSort (s', kd) ->
       (match equal_kind s'.sym_kind st'.sort_kind with
        | Eq -> kd
        | Nq -> assert false)
     | _ -> assert false)
  | StApplyTerm (st, tm') ->
    Hashtbl.hash ("StApplyTerm", st.sort_hash, tm'.term_hash),
    (match st.sort_kind.kind_desc with
     | KdArrowTerm (v', kd) ->
       (match equal_kind v'.var_kind tm'.term_sort.sort_kind with
        | Eq -> kd
        | Nq -> assert false)
     | _ -> assert false)
  | StProductSort (s, st) ->
    Hashtbl.hash ("StProductSort", s.sym_hash, st.sort_hash),
    st.sort_kind
  | StProductTerm (v, st) ->
    Hashtbl.hash ("StProductTerm", v.var_hash, st.sort_hash),
    st.sort_kind
  | StConstant (cn, array) ->
    Hashtbl.hash ("StConstant", cn.cnst_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n:(Array.length array) cn.cnst_type)
  | StInductive ((iv, int), array) ->
    Hashtbl.hash ("StInductive", iv.indv_hash, int, hash_sort_or_term_array array),
    fst (get_arrows ~n:(Array.length array) iv.indv_body.mind_bodies.(int).oind_kind)
  | StPrimitive (pm, kd, array) ->
    Hashtbl.hash ("StPrimitive", pm, kd.kind_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n:(Array.length array) kd)
  | StCase (cs, tm, sorts) ->
    Hashtbl.hash ("StCase", cs.case_hash, tm.term_hash, Array.map (fun st -> st.sort_hash) sorts),
    cs.case_type


and mk_sort : type a. a sort_desc -> a sort =
  fun sort_desc ->
  let sort_hash, sort_kind = sort_hash_kind sort_desc in
  match sort_desc with
  | StApplySort (fn, st) ->
    (match fn.sort_desc with
     | StLambdaSort (s, bd) ->
       (match equal_kind s.sym_kind st.sort_kind with
        | Eq -> subst_sym_sort s st empty bd
        | Nq -> assert false)
     | _ -> { sort_hash; sort_kind; sort_desc })
  | StApplyTerm (fn, tm) ->
    (match fn.sort_desc with
     | StLambdaTerm (v, bd) ->
       (match equal_kind v.var_kind tm.term_kind with
        | Eq -> subst_var_sort v tm empty bd
        | Nq -> assert false)
     | _ -> { sort_hash; sort_kind; sort_desc })
  | _ -> { sort_hash; sort_kind; sort_desc }


and term_hash_kind_sort : type a. a term_desc -> int * a kind * a sort =
  fun term_desc ->
  match term_desc with
  | TmTrue -> Hashtbl.hash "TmTrue", mk_kind_prop, mk_sort StTrue
  | TmBool bool -> Hashtbl.hash ("TmBool", bool), mk_kind_set, mk_sort StBool
  | TmInt int -> Hashtbl.hash ("TmInt", int), mk_kind_set, mk_sort StInt
  | TmFloat float -> Hashtbl.hash ("TmFloat", float), mk_kind_set, mk_sort StInt
  | TmArray (array, tm) ->
    Hashtbl.hash ("TmArray", Array.map (fun tm -> tm.term_hash) array, tm.term_hash),
    mk_kind_set,
    mk_sort (StArray tm.term_sort)
  | TmVariable (v, array) ->
    let n = Array.length array in
    Hashtbl.hash ("TmVariable", v.var_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n v.var_kind),
    fst (get_products ~n v.var_sort)
  | TmLambdaSort (s, tm) ->
    Hashtbl.hash ("TmLambdaSort", s.sym_hash, tm.term_hash),
    mk_kind_arrow_sort s tm.term_kind,
    mk_sort (StProductSort (s, tm.term_sort))
  | TmLambdaTerm (v, tm) ->
    Hashtbl.hash ("TmLambdaTerm", v.var_hash, tm.term_hash),
    mk_kind_arrow_term v tm.term_kind,
    mk_sort (StProductTerm (v, tm.term_sort))
  | TmApplySort (tm, st') ->
    (match tm.term_kind.kind_desc, (sort_of_constant tm.term_sort).sort_desc with
     | KdArrowSort (s', kd), StProductSort (s, st) ->
       (match
          equal_kind s.sym_kind st'.sort_kind,
          equal_kind s.sym_kind s'.sym_kind
        with
        | Eq, Eq ->
          Hashtbl.hash ("TmApplySort", tm.term_hash, st'.sort_hash),
          kd, st
        | _, _ -> assert false)
     | _ -> assert false)
  | TmApplyTerm (tm, tm') ->
    (match tm.term_kind.kind_desc, (sort_of_constant tm.term_sort).sort_desc with
     | KdArrowTerm (v',kd), StProductTerm (v, st) ->
       (match
          equal_kind v.var_kind tm'.term_kind,
          equal_kind v.var_kind v'.var_kind
        with
        | Eq, Eq ->
          Hashtbl.hash ("TmApplyTerm", tm.term_hash, tm'.term_hash),
          kd, st
        | _, _ -> assert false)
     | _ -> assert false)
  | TmConstant (cn, array) ->
    let n = Array.length array in
    Hashtbl.hash ("TmConstant", cn.cnst_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n (term_kind_of_sort cn.cnst_type)),
    fst (get_products ~n cn.cnst_type)
  | TmConstruct ((iv, int1 as indv), int2, array) ->
    let st = mk_sort (StInductive (indv, Array.sub array 0 iv.indv_body.mind_npars)) in
    Hashtbl.hash ("TmConstruct", iv.indv_hash, int1, int2, hash_sort_or_term_array array),
    term_kind_of_sort st,
    st
  | TmProject (pj, tm) ->
    (match pj.proj_sort.sort_desc with
     | StProductTerm (v, st) ->
       (match equal_kind v.var_kind tm.term_kind with
        | Eq ->
          Hashtbl.hash ("TmProject", pj.proj_hash, pj.proj_sort, tm.term_hash),
          term_kind_of_sort st,
          st
        | Nq -> assert false)
     | _ -> assert false)
  | TmPrimitive (pm, st, array) ->
    let n = Array.length array in
    Hashtbl.hash ("TmPrimitive", pm, st.sort_hash, hash_sort_or_term_array array),
    fst (get_arrows ~n (term_kind_of_sort st)),
    fst (get_products ~n st)
  | TmCase (cs, tm, terms) ->
    Hashtbl.hash ("TmCase", cs.case_hash, tm.term_hash, Array.map (fun tm -> tm.term_hash) terms),
    term_kind_of_sort cs.case_type,
    cs.case_type


and mk_term : type a. a term_desc -> a term =
  fun term_desc ->
  let term_hash, term_kind, term_sort = term_hash_kind_sort term_desc in
  match term_desc with
  | TmApplySort (fn, st) ->
    (match fn.term_desc with
     | TmLambdaSort (s, bd) ->
       (match equal_kind s.sym_kind st.sort_kind with
        | Eq -> subst_sym_term s st empty bd
        | Nq -> assert false)
     | _ -> { term_hash; term_kind; term_sort; term_desc })
  | TmApplyTerm (fn, tm) ->
    (match fn.term_desc with
     | TmLambdaTerm (v, bd) ->
       (match equal_kind v.var_kind tm.term_kind with
        | Eq -> subst_var_term v tm empty bd
        | Nq -> assert false)
     | _ -> { term_hash; term_kind; term_sort; term_desc })
  | _ -> { term_hash; term_kind; term_sort; term_desc }


and sort_of_constant : type a. a sort -> a sort =
  fun sort ->
  match sort.sort_desc with
  | StConstant (cn, array) ->
    (match cn.cnst_body with
     | None -> sort
     | Some sort ->
       sort_of_constant
         (Array.fold_left
            (fun (sort: a sort) sort_or_term ->
               match witness sort.sort_kind with
               | Prop ->
                 (match sort_or_term with
                  | Sort st -> mk_sort (StApplySort (sort, st))
                  | Term tm -> mk_sort (StApplyTerm (sort, tm)))
               | Set ->
                 (match sort_or_term with
                  | Sort st -> mk_sort (StApplySort (sort, st))
                  | Term _  -> assert false))
            sort array))
  | _ -> sort

(******************************************************************************)

let rec drop_lambda n t =
  if n > 0 then
    match t.Cic.term_desc with
    |Cic.Lambda (_, _, t) -> drop_lambda (n-1) t
    | _ -> None
  else Some t


let to_string t =
  Cic.pp_term Format.str_formatter t;
  Format.flush_str_formatter ()

let failure_extract_kind t : any_kind Result.t =
  failure (fun fmt -> fmt "Omega.extract_kind %s" (to_string t))
let failure_extract_sort t : any_sort Result.t =
  failure (fun fmt -> fmt "Omega.extract_sort %s" (to_string t))
let failure_extract_term t : any_term Result.t =
  failure (fun fmt -> fmt "Omega.extract_term %s" (to_string t))


let ok_kind kd = Ok (AnyKind kd)
let ok_sort st = Ok (AnySort st)
let ok_term tm = Ok (AnyTerm tm)


let rec is_kind env tm =
  match tm.Cic.term_desc with
  | Cic.Rel _ -> false
  | Cic.Sort s ->
    (match s with
     | Cic.Prop -> true
     | Cic.Set  -> true
     | Cic.Type -> true)
  | Cic.Product (nm, ty, bd) -> is_kind (add_cic nm ty env) bd
  | Cic.Lambda  (nm, ty, bd) -> is_kind (add_cic nm ty env) bd
  | Cic.LetIn (nm, ty, _, bd) -> is_kind (add_cic nm ty env) bd
  | Cic.App (f, _) -> is_kind env f
  | Cic.Constant _ -> false
  | Cic.Inductive _ -> false
  | Cic.Construct (_, _) -> false
  | Cic.Project (_, _) -> false
  | Cic.Case (_, _, _, _) -> false
  | Cic.Int _ -> false
  | Cic.Float _ -> false
  | Cic.Array _ -> false
  | Cic.Primitive _ -> false

let rec is_sort env tm =
  match tm.Cic.term_desc with
  | Cic.Rel string ->
    (match find_cic string env with
     | Some tm -> is_kind env tm
     | None -> assert false)
  | Cic.Sort _ -> false
  | Cic.Product (nm, ty, bd) -> is_sort (add_cic nm ty env) bd
  | Cic.Lambda  (nm, ty, bd) -> is_sort (add_cic nm ty env) bd
  | Cic.LetIn (nm, ty, _, bd) -> is_sort (add_cic nm ty env) bd
  | Cic.App (f, _) -> is_sort env f
  | Cic.Constant cn -> is_kind env cn.cnst_type
  | Cic.Inductive _ -> true
  | Cic.Construct (_, _) -> false
  | Cic.Project (pj, _) -> is_kind env (let _,_,ty = Cic.get_projection_body pj in ty)
  | Cic.Case (_, _, ty, _) -> is_kind env ty
  | Cic.Int _ -> false
  | Cic.Float _ -> false
  | Cic.Array _ -> false
  | Cic.Primitive (pm,_) ->
    (match pm with
     | Primitive.Relation _ -> true
     | Primitive.Constant _ -> false)

let rec is_term env tm =
  match tm.Cic.term_desc with
  | Cic.Rel string ->
    (match find_cic string env with
     | Some tm -> is_sort env tm
     | None -> assert false)
  | Cic.Sort _ -> false
  | Cic.Product (nm, ty, bd) -> is_term (add_cic nm ty env) bd
  | Cic.Lambda  (nm, ty, bd) -> is_term (add_cic nm ty env) bd
  | Cic.LetIn (nm, ty, _, bd) -> is_term (add_cic nm ty env) bd
  | Cic.App (f, _) -> is_term env f
  | Cic.Constant cn -> is_sort env cn.cnst_type
  | Cic.Inductive _ -> false
  | Cic.Construct (_, _) -> true
  | Cic.Project (pj, _) -> is_sort env (let _,_,ty = Cic.get_projection_body pj in ty)
  | Cic.Case (_, _, ty, _) -> is_sort env ty
  | Cic.Int _ -> true
  | Cic.Float _ -> true
  | Cic.Array _ -> true
  | Cic.Primitive (pm,_) ->
    (match pm with
     | Primitive.Relation _ -> false
     | Primitive.Constant _ -> true)


let freshen array =
  Array.map
    (function
      | Sym s -> Sym (mk_symbol (Name.fresh ()) s.sym_kind)
      | Var v -> Var (mk_variable (Name.fresh ()) v.var_kind v.var_sort))
    array

let rec sort_or_term_of_sym_or_var = function
  | Sym s ->
    eta_expand_sort
      (fun array -> ok_sort (mk_sort (StSymbol (s, array))))
      (get_arrows s.sym_kind |> snd)
    >>= fun (AnySort sort) -> Ok (Sort sort)
  | Var v ->
    eta_expand_term
      (fun array -> ok_term (mk_term (TmVariable (v, array))))
      (get_arrows v.var_kind |> snd)
    >>= fun (AnyTerm term) -> Ok (Term term)

and eta_expand_sort sort array =
  let array = freshen array in
  Result.Array.map sort_or_term_of_sym_or_var array >>= fun array' ->
  Result.Array.fold_right
    (fun sym_or_var (AnySort st) ->
       match sym_or_var with
       | Sym s -> ok_sort (mk_sort (StLambdaSort (s, st)))
       | Var v ->
         match witness st.sort_kind with
         | Prop -> ok_sort (mk_sort (StLambdaTerm (v, st)))
         | Set  -> failure (fun _ -> "Lambdas with dependent types are not (yet) supported"))
    array (sort array')

and eta_expand_term term array =
  let array = freshen array in
  Result.Array.map sort_or_term_of_sym_or_var array >>= fun array' ->
  Result.Array.fold_right
    (fun sym_or_var (AnyTerm tm) ->
       match sym_or_var with
       | Sym s -> ok_term (mk_term (TmLambdaSort (s, tm)))
       | Var v -> ok_term (mk_term (TmLambdaTerm (v, tm))))
    array (term array')


let are_parameters_or_ground_variables npars array =
  let bool = ref true in
  Array.iteri
    (fun i sym_or_var ->
       bool := !bool &&
               (i < npars ||
                match sym_or_var with
                | Sym _ -> false
                | Var v -> is_ground v.var_kind))
    array;
  !bool


let rec extract_kind env t : any_kind Result.t =
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_term")
    ~body:(fun fmt -> fmt "%a" Cic.pp_term t);*)
  match t.Cic.term_desc with
  | Cic.Sort s ->
    (match s with
     | Cic.Prop -> ok_kind mk_kind_prop
     | Cic.Set  -> ok_kind mk_kind_set
     | Cic.Type -> ok_kind mk_kind_set)

  | Cic.Product (nm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_kind env ty then
       extract_kind env ty >>= fun (AnyKind kd) ->
       let s = mk_symbol nm kd in
       extract_kind (add_sym s env) bd >>= fun (AnyKind bd) ->
       ok_kind (mk_kind_arrow_sort s bd)
     else if is_sort env ty then
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_kind (add_var v env) bd >>= fun (AnyKind bd) ->
       ok_kind (mk_kind_arrow_term v bd)
     else
       failure_extract_kind t)

  | _ -> failure_extract_kind t


and extract_sort env t : any_sort Result.t =
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_term")
    ~body:(fun fmt -> fmt "%a" Cic.pp_term t);*)
  match t.Cic.term_desc with
  | Cic.Rel string ->
    (match find_sym string env with
     | Some (AnySym sym) ->
       eta_expand_sort
         (fun array -> ok_sort (mk_sort (StSymbol (sym, array))))
         (get_arrows sym.sym_kind |> snd)
     | None -> assert false)

  | Cic.Sort _ -> failure_extract_sort t

  | Cic.Product (nm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_kind env ty then
       extract_kind env ty >>= fun (AnyKind kd) ->
       let s = mk_symbol nm kd in
       extract_sort (add_sym s env) bd >>= fun (AnySort bd) ->
       ok_sort (mk_sort (StProductSort (s, bd)))
     else if is_sort env ty then
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_sort (add_var v env) bd >>= fun (AnySort bd) ->
       ok_sort (mk_sort (StProductTerm (v, bd)))
     else
       failure_extract_sort t)

  | Cic.Lambda (nm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_kind env ty then
       extract_kind env ty >>= fun (AnyKind kd) ->
       let s = mk_symbol nm kd in
       extract_sort (add_sym s env) bd >>= fun (AnySort bd) ->
       ok_sort (mk_sort (StLambdaSort (s, bd)))
     else if is_sort env ty then
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_sort (add_var v env) bd >>= fun (AnySort bd) ->
       match witness bd.sort_kind with
       | Prop -> ok_sort (mk_sort (StLambdaTerm (v, bd)))
       | Set  -> failure (fun _ -> "Lambdas with dependent types are not (yet) supported")
     else
       failure_extract_sort t)

  | Cic.LetIn (nm, tm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_sort env tm && is_kind env ty then
       extract_sort env tm >>= fun (AnySort tm) ->
       extract_kind env ty >>= fun (AnyKind ty) ->
       let s = mk_symbol nm ty in
       extract_sort (add_sym s env) bd >>= fun (AnySort bd) ->
       match equal_witness (witness s.sym_kind) (witness tm.sort_kind) with
       | Eq -> ok_sort (subst_sym_sort s tm empty bd)
       | Nq -> failure_extract_sort t
     else if is_term env tm && is_sort env ty then
       extract_term env tm >>= fun (AnyTerm tm) ->
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_sort (add_var v env) bd >>= fun (AnySort bd) ->
       match witness bd.sort_kind with
       | Set -> failure (fun _ -> "LetIns with dependent types are not (yet) supported")
       | Prop ->
         match equal_witness (witness v.var_kind) (witness tm.term_kind) with
         | Eq -> ok_sort (subst_var_sort v tm empty bd)
         | Nq -> failure_extract_sort t
     else
       failure_extract_sort t)

  | Cic.App (f, array) ->
    extract_sort env f >>= fun (AnySort f) ->
    Result.Array.fold_left
      (fun (AnySort st) tm ->
         if is_sort env tm then
           extract_sort env tm >>= fun (AnySort tm) ->
           ok_sort (mk_sort (StApplySort (st, tm)))
         else if is_term env tm then
           extract_term env tm >>= fun (AnyTerm tm) ->
           match witness st.sort_kind with
           | Prop -> ok_sort (mk_sort (StApplyTerm (st, tm)))
           | Set  -> failure (fun _ -> "Apps with dependent types are not (yet) supported")
         else
           failure_extract_sort t)
      (ok_sort f) array

  | Cic.Constant cn ->
    extract_kind env cn.cnst_type >>= fun (AnyKind kd) ->
    eta_expand_sort
      (fun array ->
         match cn.cnst_ident with
         | "array", ["Array"; "Extractor"] ->
           (match array.(0) with
            | Sort sort ->
              (match witness sort.sort_kind with
               | Prop -> failure_extract_sort t
               | Set  -> ok_sort (mk_sort (StArray sort)))
            | _ -> failure_extract_sort t)
         | _ ->
           match cn.cnst_body with
           | Some ty ->
             extract_sort env ty >>= fun (AnySort ty) ->
             (match equal_kind kd ty.sort_kind with
              | Eq ->
                (match witness kd with
                 | Prop -> ok_sort (mk_sort (StConstant (mk_constant cn.cnst_ident kd (Some ty), array)))
                 | Set  -> ok_sort (Array.fold_left sort_apply_sort_or_term ty array))
              | Nq -> failure_extract_sort t)
           | None ->
             ok_sort (mk_sort (StConstant (mk_constant cn.cnst_ident kd None, array))))
      (get_arrows kd |> snd)

  | Cic.Inductive (iv,int) ->
    (match fst iv.indv_ident with
     | "True"  -> ok_sort (mk_sort StTrue)
     | "False" -> ok_sort (mk_sort StFalse)
     | "nat"   -> ok_sort (mk_sort StInt)
     | _ ->
       extract_inductive env iv >>= fun (AnyInductive iv) ->
       let _, array = get_arrows (*~n:iv.indv_body.mind_npars*) iv.indv_body.mind_bodies.(int).oind_kind in
       (*assert (Array.length array = iv.indv_body.mind_npars);*)
       eta_expand_sort
         (fun array -> ok_sort (mk_sort (StInductive ((iv, int), array))))
         array)

  | Cic.Construct _ -> failure_extract_sort t

  | Cic.Project (pj,_) ->
    failure (fun fmt ->
        fmt "%s Primitive records with fields in Prop, Set or Type are not (yet) supported"
          pj.proj_name
      )

  | Cic.Case (cs, tm, ty, array) -> 
    (match drop_lambda 1 ty with
     | None -> assert false
     | Some ty ->
       extract_term env tm >>= fun (AnyTerm tm) ->
       extract_kind env ty >>= fun (AnyKind kd) ->
       extract_case env cs kd >>= fun (AnyCase cs) ->
       match witness kd with
       | Set  -> failure (fun _ -> "Cases with dependent types are not (yet) supported")
       | Prop ->
         Result.Array.map (extract_sort env) array >>= fun array ->
         Result.Array.map (unpack_sort Prop) array >>= fun array ->
         match
           equal_witness
             (witness tm.term_kind)
             (witness (fst cs.case_indv).indv_body.mind_bodies.(snd cs.case_indv).oind_kind)
         with
         | Eq -> ok_sort (mk_sort (StCase (cs, tm, array)))
         | Nq -> failure_extract_sort t)

  | Cic.Primitive (pm, kd) ->
    extract_kind env kd >>= fun (AnyKind kd) ->
    eta_expand_sort
      (fun array ->
         (match pm, witness kd with
          | Primitive.(Relation pm), Prop->
            ok_sort (mk_sort (StPrimitive (pm, kd, array)))
          | _, _ -> failure_extract_sort t))
      (get_arrows kd |> snd)

  | Cic.Int   _ -> failure_extract_sort t
  | Cic.Float _ -> failure_extract_sort t
  | Cic.Array _ -> failure_extract_sort t


and extract_term env t : any_term Result.t =
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_term")
    ~body:(fun fmt -> fmt "%a" Cic.pp_term t);*)
  match t.Cic.term_desc with
  | Cic.Rel name ->
    (match find_var name env with
     | Some (AnyVar var) ->
       eta_expand_term
         (fun array -> ok_term (mk_term (TmVariable (var, array))))
         (get_arrows var.var_kind |> snd)
     | None -> assert false)

  | Cic.Sort _ -> failure_extract_term t

  | Cic.Product _ -> failure_extract_term t

  | Cic.Lambda (nm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_kind env ty then
       extract_kind env ty >>= fun (AnyKind kd) ->
       let s = mk_symbol nm kd in
       extract_term (add_sym s env) bd >>= fun (AnyTerm bd) ->
       ok_term (mk_term (TmLambdaSort (s, bd)))
     else if is_sort env ty then
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_term (add_var v env) bd >>= fun (AnyTerm bd) ->
       ok_term (mk_term (TmLambdaTerm (v, bd)))
     else
       failure_extract_term t)

  | Cic.LetIn (nm, tm, ty, bd) ->
    let env = add_cic nm ty env in
    (if is_sort env tm && is_kind env ty then
       extract_sort env tm >>= fun (AnySort tm) ->
       extract_kind env ty >>= fun (AnyKind ty) ->
       let s = mk_symbol nm ty in
       extract_term (add_sym s env) bd >>= fun (AnyTerm bd) ->
       match equal_witness (witness s.sym_kind) (witness tm.sort_kind) with
       | Eq -> ok_term (subst_sym_term s tm empty bd)
       | Nq -> failure_extract_term t
     else if is_term env tm && is_sort env ty then
       extract_term env tm >>= fun (AnyTerm tm) ->
       extract_sort env ty >>= fun (AnySort ty) ->
       let v = mk_variable nm (term_kind_of_sort ty) ty in
       extract_term (add_var v env) bd >>= fun (AnyTerm bd) ->
       match equal_witness (witness v.var_kind) (witness tm.term_kind) with
       | Eq -> ok_term (subst_var_term v tm empty bd)
       | Nq -> failure_extract_term t
     else
       failure_extract_term t)

  | Cic.App (f, array) ->
    extract_term env f >>= fun (AnyTerm f) ->
    Result.Array.fold_left
      (fun (AnyTerm tm) t ->
         if is_sort env t then
           extract_sort env t >>= fun (AnySort t) ->
           ok_term (mk_term (TmApplySort (tm, t)))
         else if is_term env t then
           extract_term env t >>= fun (AnyTerm t) ->
           ok_term (mk_term (TmApplyTerm (tm, t)))
         else
           failure_extract_term t)
      (ok_term f) array

  | Cic.Constant cn ->
    extract_sort env cn.cnst_type >>= fun (AnySort st) ->
    eta_expand_term
      (fun array ->
         match cn.cnst_body with
         | Some tm ->
           extract_term env tm >>= fun (AnyTerm tm) ->
           (match equal_kind (term_kind_of_sort st) tm.term_kind with
            | Eq -> ok_term (mk_term (TmConstant (mk_constant cn.cnst_ident st (Some tm), array)))
            | Nq -> failure_extract_term t)
         | None ->
           ok_term (mk_term (TmConstant (mk_constant cn.cnst_ident st None, array))))
      (get_products st |> snd)

  | Cic.Inductive _ -> failure_extract_term t

  | Cic.Construct ((iv, int1), int2) ->
    extract_inductive env iv >>= fun (AnyInductive iv) ->
    let oi = iv.indv_body.mind_bodies.(int1) in
    let _, array = get_products (*~n:oi.oind_ctors.(int2).ctor_nargs*) oi.oind_ctors.(int2).ctor_sort in
    eta_expand_term
      (fun array -> ok_term (mk_term (TmConstruct ((iv, int1),int2, array))))
      array

  | Cic.Project (pj, tm) ->
    extract_projection env pj >>= fun (AnyProjection pj) ->
    extract_term env tm >>= fun (AnyTerm tm) ->
    (match
       equal_witness
         (witness (fst pj.proj_indv).indv_body.mind_bodies.(snd pj.proj_indv).oind_kind)
         (witness tm.term_kind)
     with
     | Eq -> ok_term (mk_term (TmProject (pj, tm)))
     | Nq -> failure_extract_term t)

  | Cic.Case (cs, tm, ty, array) ->
    (match drop_lambda 1 ty with
     | None -> assert false
     | Some ty ->
       extract_term env tm >>= fun (AnyTerm tm) ->
       extract_sort env ty >>= fun (AnySort st) ->
       extract_case env cs st >>= fun (AnyCase cs) ->
       Result.Array.map (extract_term env) array >>= fun array ->
       Result.Array.map (unpack_term (witness st.sort_kind)) array >>= fun array ->
       match
         equal_witness
           (witness tm.term_kind)
           (witness (fst cs.case_indv).indv_body.mind_bodies.(snd cs.case_indv).oind_kind)
       with
       | Eq -> ok_term (mk_term (TmCase (cs, tm, array)))
       | Nq -> failure_extract_term t)

  | Cic.Int int -> ok_term (mk_term (TmInt int))
  | Cic.Float float -> ok_term (mk_term (TmFloat float))
  | Cic.Array (array, tm, ty) ->
    extract_term env tm >>= fun (AnyTerm tm) ->
    extract_sort env ty >>= fun (AnySort st) ->
    Result.Array.map (extract_term env) array >>= fun array ->
    Result.Array.map (unpack_term Set) array >>= fun array ->
    (match equal_witness (witness tm.term_kind) Set, equal_witness (witness st.sort_kind) Set with
     | Eq, Eq -> ok_term (mk_term (TmArray (array, tm)))
     | _, _ -> failure_extract_term t)

  | Cic.Primitive (pm, st) ->
    extract_sort env st >>= fun (AnySort st) ->
    eta_expand_term
      (fun array ->
         (match pm, witness st.sort_kind with
          | Primitive.(Constant pm), Set ->
            ok_term (mk_term (TmPrimitive (pm, st, array)))
          | _, _ -> failure_extract_term t))
      (get_products st |> snd)


and extract_inductive env Cic.{ indv_ident; indv_body; _ } : any_inductive Result.t =
  let string = ident_to_string indv_ident in
  if indv_body.mind_npars <> indv_body.mind_npars_rec then
    failure (fun fmt ->
        fmt "In %s, non-uniform inductive parameters are not (yet) supported.\n\
             Use 'Set Uniform Inductive Parameters.' to avoid this issue."
          string)
  else if Array.length indv_body.mind_bodies > 1 then
    failure (fun fmt ->
        fmt "In %s, mutually recursive inductives are not (yet) supported."
          string)
  else
    match find_ind string env with
    | Some indv -> Ok indv
    | None ->
      let Cic.{ oind_type; _ } = indv_body.Cic.mind_bodies.(0) in
      extract_kind env oind_type >>= fun (AnyKind oind_kind) ->
      let witness = witness oind_kind in
      extract_mutual_inductive extract_dummy_one_inductive witness env indv_body >>= fun mind ->
      unpack_mutual_inductive witness 0 mind >>= fun mind ->
      let indv = mk_inductive indv_ident mind in
      let env = add_ind indv env in
      extract_mutual_inductive extract_one_inductive witness env indv_body >>= fun mind ->
      unpack_mutual_inductive witness 0 mind >>= fun mind ->
      indv.indv_body <- mind;
      Log.Verbose.debug
        ~head:(fun fmt -> fmt "extract_inductive")
        ~body:(fun fmt -> fmt "%a" pp_inductive indv);
      Ok (AnyInductive indv)
(*
  if match witness with Prop -> true | Set -> indv_body.mind_finite <> Cic.BiFinite then
  else failure (fun fmt ->
      fmt "In %s, 'Inductive' in Set or Type are not (yet) supported.\n\
           Use 'Record' or 'Variant' instead."
        string)
*)

and extract_mutual_inductive :
  'a. ('a witness -> int -> env -> Cic.one_inductive -> any_one_inductive Result.t) ->
  'a witness -> env -> Cic.mutual_inductive -> any_mutual_inductive Result.t =
  fun f wt env Cic.{ mind_npars; mind_bodies; _ } ->
  Result.Array.map (f wt mind_npars env) mind_bodies >>= fun mind_bodies ->
  Result.Array.map (unpack_one_inductive wt) mind_bodies >>= fun mind_bodies ->
  Ok (AnyMutualInductive (mk_mutual_inductive mind_npars mind_bodies))


and extract_dummy_one_inductive :
  type a. a witness -> int -> env -> Cic.one_inductive -> any_one_inductive Result.t =
  fun wt npars env Cic.{ oind_name; oind_type; _ } ->
  extract_kind env oind_type >>= fun oind_kind ->
  unpack_kind wt oind_kind >>= fun oind_kind ->
  if not (are_parameters_or_ground_variables npars (snd (get_arrows oind_kind))) then
    failure (fun fmt ->
        fmt "In %s, inductive type annotations are restricted to ground types."
          oind_name)
  else
    Ok (AnyOneInductive (mk_one_inductive oind_name oind_kind [||]))


and extract_one_inductive :
  type a. a witness -> int -> env -> Cic.one_inductive -> any_one_inductive Result.t =
  fun wt npars env Cic.{ oind_name; oind_type; oind_nargs; oind_ndecls; oind_ctors; _ } ->
  extract_kind env oind_type >>= fun oind_kind ->
  unpack_kind wt oind_kind >>= fun oind_kind ->
  match wt with
  | Set when oind_nargs <> 0 || oind_ndecls <> 0 ->
    failure (fun fmt ->
        fmt "In %s, annotated inductive types are not (yet) supported.\n\
             Use (uniformly) parameterized inductive types instead."
          oind_name)
  | _ ->
    if not (are_parameters_or_ground_variables npars (snd (get_arrows oind_kind))) then
      failure (fun fmt ->
          fmt "In %s, inductive type annotations are restricted to ground types."
            oind_name)
    else
      Result.Array.map (extract_constructor npars env) oind_ctors >>= fun oind_ctors ->
      Result.Array.map (unpack_constructor wt) oind_ctors >>= fun oind_ctors ->
      Ok (AnyOneInductive (mk_one_inductive oind_name oind_kind oind_ctors))


and extract_constructor : int -> env -> Cic.constructor -> any_constructor Result.t =
  fun npars env Cic.{ ctor_name; ctor_type; ctor_nargs; ctor_ndecls; _ } ->
  if ctor_nargs <> ctor_ndecls then
    Log.warning (fun fmt ->
        fmt "In %s, local definitions in type of constructors are not (fully) supported."
          ctor_name);
  extract_sort env ctor_type >>= fun (AnySort ctor_sort) ->
  let ctor_kind = term_kind_of_sort ctor_sort in
  if not (are_parameters_or_ground_variables npars (snd (get_products ctor_sort))) then
    failure (fun fmt ->
        fmt "In %s, constructor arguments are restricted to ground variables."
          ctor_name)
  else
    Ok (AnyConstructor (mk_constructor ctor_name ctor_kind ctor_sort ctor_nargs))


and extract_projection : env -> Cic.projection -> any_projection Result.t =
  fun env (Cic.{ proj_indv; proj_name; proj_arg; _  } as proj) ->
  extract_inductive env (fst proj_indv) >>= fun (AnyInductive indv) ->
  extract_sort env (let _,_,ty = Cic.get_projection_body proj in ty) >>= fun (AnySort proj_type) ->
  Ok (AnyProjection (mk_projection (indv, snd proj_indv) proj_name proj_type proj_arg))


and extract_case : 'a. env -> Cic.case -> 'a -> 'a any_case Result.t =
  fun env Cic.{ case_ndecls; case_nargs; case_indv; _ } case_type ->
  if Array.exists2 (<>) case_ndecls case_nargs then
    Log.warning (fun fmt ->
        fmt "Local definitions in pattern-matchings are not (fully) supported.");
  extract_inductive env (fst case_indv) >>= fun (AnyInductive indv) ->
  Ok (AnyCase (mk_case (indv, snd case_indv) case_type case_nargs))


let extract_relation : Cic.term -> (prop inductive * int) Result.t =
  fun term ->
  match term.term_desc with
  | Inductive (indv, int) ->
    extract_inductive (create 17) indv >>= fun (AnyInductive indv) ->
    (match witness indv.indv_body.mind_bodies.(int).oind_kind with
     | Prop -> Ok ((indv : prop inductive), int)
     | Set  -> failure (fun _ -> "This inductive has kind Set but was expected of kind Prop"))
  | _ -> failure (fun _ -> "Not an inductive")

let extract_datatype : Cic.term -> (set inductive * int) Result.t =
  fun term ->
  match term.term_desc with
  | Inductive (indv, int) ->
    extract_inductive (create 17) indv >>= fun (AnyInductive indv) ->
    (match witness indv.indv_body.mind_bodies.(int).oind_kind with
     | Prop -> failure (fun _ -> "This inductive has kind Prop but was expected of kind Set")
     | Set -> Ok ((indv : set inductive), int))
  | _ -> failure (fun _ -> "Not an inductive")


let extract_lemma : Cic.term -> (prop sort,prop term) constant Result.t =
  fun term ->
  match term.term_desc with
  | Constant cn ->
    let env = create 17 in
    extract_sort env cn.cnst_type >>= fun (AnySort st) ->
    (match witness st.sort_kind with
     | Prop ->
       (match cn.cnst_body with
        | Some tm ->
          extract_term env tm >>= fun (AnyTerm tm) ->
          (match equal_kind (term_kind_of_sort st) tm.term_kind with
           | Eq -> Ok (mk_constant cn.cnst_ident st (Some tm) : (prop sort,prop term) constant)
           | Nq -> assert false)
        | None -> Ok (mk_constant cn.cnst_ident st None : (prop sort,prop term) constant))
     | Set  -> failure (fun _ -> "This constant has kind Set but was expected of kind Prop"))
  | _ -> failure (fun _ -> "Not a constant")

