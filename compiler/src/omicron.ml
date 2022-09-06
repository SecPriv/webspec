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
      let name = "omicron"
    end)

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

and sym_or_var = Sym : _ sym -> sym_or_var | Var : _ var -> sym_or_var

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
  | StProductSort : _ sym * 'a sort -> 'a sort_desc
  | StProductTerm : _ var * 'a sort -> 'a sort_desc
  | StConstant    : ('a kind,'a sort) constant * sort_or_term array -> 'a sort_desc
  | StInductive   : ('a inductive * int)       * sort_or_term array -> 'a sort_desc
  | StPrimitive   : Primitive.relation  * 'a kind * sort_or_term array -> 'a sort_desc
  | StCase        : ('a,prop kind,prop sort) case * 'a term -> prop sort_desc

and 'a term = {
  term_hash : int;
  term_kind : 'a kind;
  term_sort : 'a sort;
  term_desc : 'a term_desc;
}

and _ term_desc =
  | TmTrue      : prop term_desc
  | TmBool      : bool  -> set term_desc
  | TmInt       : int   -> set term_desc
  | TmFloat     : float -> set term_desc
  | TmArray     : set term array * set term -> set term_desc

  | TmVariable  : 'a var * sort_or_term array -> 'a term_desc
  | TmConstant  : ('a sort,'a term) constant * sort_or_term array -> 'a term_desc
  | TmConstruct : ('a inductive * int) * int * sort_or_term array -> 'a term_desc
  | TmProject   : ('a,'b) projection * 'a term -> 'b term_desc
  | TmPrimitive : Primitive.constant * 'a sort * sort_or_term array -> 'a term_desc
  | TmCase      : ('a,'b sort,'b term) case * 'a term -> 'b term_desc

and sort_or_term = Sort : _ sort -> sort_or_term | Term : _ term -> sort_or_term

and ('a,'b) constant = {
  cnst_hash : int;
  cnst_ident: ident;
  cnst_prms : sym_or_var array;
  cnst_type : 'a;
  cnst_body : 'b option;
}

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

and ('a,'b,'c) case = {
  case_hash : int;
  case_indv : 'a inductive * int;
  case_type : 'b;
  case_branches : 'c branch array;
}

and 'a branch = {
  bnch_hash : int;
  bnch_prms : sym_or_var array;
  bnch_desc : 'a;
}

(******************************************************************************)

let rec get_arrows : type a. int -> a kind -> sym_or_var list -> a kind * sym_or_var list =
  fun n kd list ->
  if n > 0 then
    match kd.kind_desc with
    | KdProp -> kd, list
    | KdSet  -> kd, list
    | KdArrowSort (s, kd) -> get_arrows (n-1) kd (Sym s :: list)
    | KdArrowTerm (v, kd) -> get_arrows (n-1) kd (Var v :: list)
  else kd, list

let get_arrows ?(n=max_int) kd =
  let kd, list = get_arrows n kd [] in
  kd, List.rev list

let rec get_products : type a. int -> a sort -> sym_or_var list -> a sort * sym_or_var list =
  fun n st list ->
  if n > 0 then
    match st.sort_desc with
    | StProductSort (s, st) -> get_products (n-1) st (Sym s :: list)
    | StProductTerm (v, st) -> get_products (n-1) st (Var v :: list)
    | _ -> st, list
  else st, list

let get_products ?(n=max_int) st =
  let st, list = get_products n st [] in
  st, List.rev list

let get_one_inductive (indv,int) = indv.indv_body.mind_bodies.(int)

(******************************************************************************)

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

and pp_sym_or_var : Format.formatter -> sym_or_var -> unit =
  fun fmt sym_or_var ->
  match sym_or_var with
  | Sym sym -> Format.fprintf fmt "@[<hov 1>(Sym@ %a)@]" pp_sym sym
  | Var var -> Format.fprintf fmt "@[<hov 1>(Var@ %a)@]" pp_var var

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
  | StProductSort (s, st) -> Format.fprintf fmt "@[<hov 1>(StProductSort@ %a@ %a)@]" pp_sym s pp_sort st
  | StProductTerm (v, st) -> Format.fprintf fmt "@[<hov 1>(StProductTerm@ %a@ %a)@]" pp_var v pp_sort st
  | StConstant (cn, array) ->
    Format.fprintf fmt "@[<hov 1>(StConstant %s:@ %a@ [@[%a@]])@]"
      (fst cn.cnst_ident)
      pp_kind cn.cnst_type
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StInductive ((iv,int), array) ->
    let oind = iv.indv_body.mind_bodies.(int) in
    Format.fprintf fmt "@[<hov 1>(StInductive %s:@ %a@ [@[%a@]])@]"
      oind.oind_name
      pp_kind oind.oind_kind
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StPrimitive (pm, kd, array) ->
    Format.fprintf fmt "@[<hov 1>(StPrimitive %s:@ %a@ [@[%a@]])@]"
      (Primitive.relation_to_string pm)
      pp_kind kd
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | StCase (cs, tm) ->
    Format.fprintf fmt "@[<hov 1>(StCase@ [@[%a@]]@ %a)@]"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (pp_branch pp_sort))
      (Array.to_list cs.case_branches)
      pp_term tm

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
    Format.fprintf fmt "@[<hov 1>(StPrimitive %s:@ %a@ [@[%a@]])@]"
      (Primitive.constant_to_string pm)
      pp_sort st
      (Format.pp_print_list pp_sort_or_term) (Array.to_list array)
  | TmCase (cs, tm) ->
    Format.fprintf fmt "@[<hov 1>(StCase@ [@[%a@]]@ %a)@]"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (pp_branch pp_term))
      (Array.to_list cs.case_branches)
      pp_term tm

and pp_sort_or_term : Format.formatter -> sort_or_term -> unit =
  fun fmt sort_or_term ->
  match sort_or_term with
  | Sort sort -> Format.fprintf fmt "@[<hov 1>(Sort@ %a)@]" pp_sort sort
  | Term term -> Format.fprintf fmt "@[<hov 1>(Term@ %a)@]" pp_term term

and pp_branch : type a. (Format.formatter -> a -> unit) -> Format.formatter -> a branch -> unit =
  fun f fmt { bnch_prms; bnch_desc; _ } ->
  Format.fprintf fmt "@[<hov 1>{bnch_prms: [@[%a@]]@\nbnch_desc: %a}@]"
    (Format.pp_print_list pp_sym_or_var) (Array.to_list bnch_prms)
    f bnch_desc

and pp_constant :
  type a b. (Format.formatter -> a -> unit) -> (Format.formatter -> b -> unit) ->
  Format.formatter -> (a,b) constant -> unit =
  fun f g fmt { cnst_ident; cnst_prms; cnst_type; cnst_body; _ } ->
  Format.fprintf fmt "@[<hov 1>{cnst_name: %a@\ncnst_prms: [@[%a@]]@\ncnst_type: %a@\ncnst_body: %a}@]"
    pp_ident cnst_ident
    (Format.pp_print_list pp_sym_or_var) (Array.to_list cnst_prms)
    f cnst_type
    (Format.pp_print_option g) cnst_body


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

let hash_sym_or_var_array array =
  Array.map (function Sym s -> s.sym_hash | Var v -> v.var_hash) array

let hash_sort_or_term_array array =
  Array.map (function Sort s -> s.sort_hash | Term t -> t.term_hash) array

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

(*
let equal_name_or_anonymous nm1 nm2 =
  match nm1, nm2 with
  | Name.Anonymous, Name.Anonymous -> true
  | Name.Id _, Name.Id _ -> true
  | Name.Name string1, Name.Name string2 -> String.equal string1 string2
  | _, _ -> false

let equal_symbol_name_kind : type a b. a sym -> b sym -> bool =
  fun s1 s2 ->
  match equal_kind s1.sym_kind s2.sym_kind with
  | Eq -> equal_name_or_anonymous s1.sym_name s2.sym_name
  | Nq -> false

let equal_variable_name_kind : type a b. a var -> b var -> bool =
  fun v1 v2 ->
  match equal_kind v1.var_kind v2.var_kind with
  | Eq -> equal_name_or_anonymous v1.var_name v2.var_name
  | Nq -> false
*)

let rec witness : type a. a kind -> a witness =
  fun kd ->
  match kd.kind_desc with
  | KdProp -> Prop
  | KdSet  -> Set
  | KdArrowSort (_, kd) -> witness kd
  | KdArrowTerm (_, kd) -> witness kd

let is_ground : type a. a kind -> bool =
  fun kind ->
  match kind.kind_desc with
  | KdProp -> true
  | KdSet  -> true
  | KdArrowSort _ -> false
  | KdArrowTerm _ -> false

let mk_kind_prop = mk_kind KdProp
let mk_kind_set  = mk_kind KdSet
let mk_kind_arrow_sort s kd = mk_kind (KdArrowSort (s, kd))
let mk_kind_arrow_term v kd = mk_kind (KdArrowTerm (v, kd))

let mk_constant cnst_ident cnst_prms cnst_type cnst_body =
  let cnst_hash = Hashtbl.hash (cnst_ident, hash_sym_or_var_array cnst_prms) in
  { cnst_hash; cnst_ident; cnst_prms; cnst_type; cnst_body }

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

let mk_case (indv,int as case_indv) case_type case_branches =
  let case_hash =
    Hashtbl.hash (indv.indv_hash, int, Array.map (fun br -> br.bnch_hash) case_branches)
  in
  { case_hash; case_indv; case_type; case_branches }

let mk_branch bnch_prms bnch_desc =
  let bnch_hash = Hashtbl.hash (hash_sym_or_var_array bnch_prms) in
  { bnch_hash; bnch_prms; bnch_desc }


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
      | StSymbol (s, _) -> s.sym_kind
      | StProductSort (s, st) -> mk_kind_arrow_sort s (term_kind_of_sort st)
      | StProductTerm (v, st) -> mk_kind_arrow_term v (term_kind_of_sort st)
      | StConstant (cn, _) -> aux cn.cnst_type
      | StInductive ((iv, int), _) -> aux iv.indv_body.mind_bodies.(int).oind_kind
      | StPrimitive (_,kd,_) -> aux kd
      | StCase (cs, _) -> aux cs.case_type
  in
  fun sort ->
    assert (is_ground sort.sort_kind);
    term_kind_of_sort sort


let sort_hash_kind : type a. a sort_desc -> int * a kind =
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
  | StCase (cs, tm) ->
    Hashtbl.hash ("StCase", cs.case_hash, tm.term_hash),
    cs.case_type


let mk_sort : type a. a sort_desc -> a sort =
  fun sort_desc ->
  let sort_hash, sort_kind = sort_hash_kind sort_desc in
  { sort_hash; sort_kind; sort_desc }


let term_hash_kind_sort : type a. a term_desc -> int * a kind * a sort =
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
  | TmCase (cs, tm) ->
    Hashtbl.hash ("TmCase", cs.case_hash, tm.term_hash),
    term_kind_of_sort cs.case_type,
    cs.case_type


let mk_term : type a. a term_desc -> a term =
  fun term_desc ->
  let term_hash, term_kind, term_sort = term_hash_kind_sort term_desc in
  { term_hash; term_kind; term_sort; term_desc }

(******************************************************************************)

type bind_sym_var =
  | BindSym : 'a sym * 'a sort -> bind_sym_var
  | BindVar : 'a var * 'a term -> bind_sym_var
(*
let pp_bind fmt bd =
  match bd with
  | BindSym (s, st) -> Format.fprintf fmt "@[<hov 1>(%a ->@ %a)@]" pp_sym s pp_sort st
  | BindVar (v, tm) -> Format.fprintf fmt "@[<hov 1>(%a ->@ %a)@]" pp_var v pp_term tm
*)
let split = function
  | BindSym (s, st) -> Sym s, Sort st
  | BindVar (v, tm) -> Var v, Term tm

type any_inductive = AnyInductive : _ inductive -> any_inductive

type env = {
  ind_map    : any_inductive StringHashtbl.t;
  parameters : sym_or_var list;
  arguments  : sort_or_term list;
  bindings   : bind_sym_var list;
}

let create n = {
  ind_map = StringHashtbl.create n;
  parameters = [];
  arguments  = [];
  bindings   = [];
}

let add_ind ind env =
  let string = ident_to_string ind.indv_ident in
  assert (not (StringHashtbl.mem env.ind_map string));
  StringHashtbl.add env.ind_map string (AnyInductive ind);
  env

let find_ind string env = StringHashtbl.find_opt env.ind_map string

let pop_argument env =
  match env.arguments with
  | [] -> None
  | arg :: arguments -> Some (arg, { env with arguments })

let push_sym sym env = { env with parameters = Sym sym :: env.parameters }
let push_var var env = { env with parameters = Var var :: env.parameters }

let flush_parameters env = List.rev env.parameters, { env with parameters = [] }

let push_sort sort env = { env with arguments = Sort sort :: env.arguments }
let push_term term env = { env with arguments = Term term :: env.arguments }

let flush_bindings env = List.rev env.bindings, { env with bindings = [] }

let bind_sym sym sort env = { env with bindings = BindSym (sym, sort) :: env.bindings }
let bind_var var term env = { env with bindings = BindVar (var, term) :: env.bindings }

let ok_sort desc = Ok (mk_sort desc)
let ok_term desc = Ok (mk_term desc)


module SymVarMap = Map.Make
    (struct
      type t = sym_or_var
      let compare t1 t2 = compare t1 t2
    end)

type sym_var_map = sort_or_term array list SymVarMap.t


let fresh_sym s _array = s
let fresh_var v _array = v

let bindings map =
  List.map
    (fun (sym_or_var, list) ->
       List.map
         (match sym_or_var with
          | Sym s -> fun array ->
            let s = fresh_sym s array in
            BindSym (s, mk_sort (StSymbol (s, array)))
          | Var v -> fun array ->
            let v = fresh_var v array in
            BindVar (v, mk_term (TmVariable (v, array))))
         (List.sort_uniq compare list))
    (SymVarMap.bindings map)
  |> List.flatten

let union map1 map2 =
  SymVarMap.union
    (fun _ list1 list2 -> Some List.(sort_uniq compare (rev_append list1 list2)))
    map1 map2

let rec free_sort : type a. a sort -> sym_var_map =
  fun sort ->
  match sort.sort_desc with
  | StTrue  -> SymVarMap.empty
  | StFalse -> SymVarMap.empty
  | StBool  -> SymVarMap.empty
  | StInt   -> SymVarMap.empty
  | StFloat -> SymVarMap.empty
  | StArray st -> free_sort st
  | StSymbol (s, array) -> free_array (SymVarMap.singleton (Sym s) [array]) array
  | StProductSort (s, st) -> SymVarMap.remove (Sym s) (free_sort st)
  | StProductTerm (v, st) -> SymVarMap.remove (Var v) (free_sort st)
  | StConstant (_, array) -> free_array SymVarMap.empty array
  | StInductive (_, array)-> free_array SymVarMap.empty array
  | StPrimitive (_, _, array) -> free_array SymVarMap.empty array
  | StCase (cs, tm) -> free_branch free_sort (free_term tm) cs.case_branches


and free_term : type a. a term -> sym_var_map =
  fun term ->
  match term.term_desc with
  | TmTrue    -> SymVarMap.empty
  | TmBool _  -> SymVarMap.empty
  | TmInt _   -> SymVarMap.empty
  | TmFloat _ -> SymVarMap.empty
  | TmArray (array, tm) ->
    Array.fold_left
      (fun set term -> union set (free_term term))
      (free_term tm) array
  | TmVariable (v, array) -> free_array (SymVarMap.singleton (Var v) [array]) array
  | TmConstant (_, array) -> free_array SymVarMap.empty array
  | TmConstruct (_, _, array) -> free_array SymVarMap.empty array
  | TmProject (_, tm) -> free_term tm
  | TmPrimitive (_, _, array) -> free_array SymVarMap.empty array
  | TmCase (cs, tm) -> free_branch free_term (free_term tm) cs.case_branches


and free_array init array =
  Array.fold_left
    (fun set sort_or_term ->
       union set
         (match sort_or_term with
          | Sort sort -> free_sort sort
          | Term term -> free_term term))
    init array


and free_branch : type a. (a -> sym_var_map) -> sym_var_map -> a branch array -> sym_var_map =
  fun free init array ->
  Array.fold_left
    (fun set bnch ->
       union set
         (Array.fold_left
            (fun set sym_or_var -> SymVarMap.remove sym_or_var set)
            (free bnch.bnch_desc)
            bnch.bnch_prms))
    init array


let fresh_closure_name =
  let cnt = ref (-1) in
  fun () -> incr cnt; Printf.sprintf "<closure%i>" !cnt, []

let closure env ty bd free =
  let bind_parameters, bind_arguments, env =
    let bindings, env = flush_bindings env in
    let parameters, env = flush_parameters env in
    let pars, args = List.split (List.map split bindings) in
    pars @ parameters, args, env
  in
  let free_parameters, free_arguments =
    List.fold_left (fun free sym_var -> SymVarMap.remove sym_var free) free bind_parameters
    |> bindings |> List.map split |> List.split
  in
  let parameters = List.concat [free_parameters; bind_parameters] |> Array.of_list in
  let arguments  = List.concat [free_arguments;  bind_arguments]  |> Array.of_list in
  match pop_argument env with
  | Some _ -> failure (fun _ -> "Omicron.closure")
  | None ->
    Ok (mk_constant (fresh_closure_name ()) parameters ty (Some bd), arguments)

let rec sort_closure : type a. env -> a Omega.sort -> a sort Result.t =
  fun env sort ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "sort_closure")
    ~body:(fun fmt -> fmt "%a" Omega.pp_sort sort);*)
  match sort.Omega.sort_desc with
  | StLambdaSort (s, sort) ->
    extract_symbol env s >>= fun s ->
    (match pop_argument env with
     | Some (Sort st, env) ->
       (match equal_kind s.sym_kind st.sort_kind with
        | Eq -> sort_closure (bind_sym s st env) sort
        | _ -> failure (fun _ -> "Omicron.sort_closure"))
     | Some _ -> assert false
     | _ -> sort_closure (push_sym s env) sort)
  | StLambdaTerm (v, sort) ->
    extract_variable env v >>= fun v ->
    (match pop_argument env with
     | Some (Term tm, env) ->
       (match equal_kind v.var_kind tm.term_kind with
        | Eq -> sort_closure (bind_var v tm env) sort
        | _ -> failure (fun _ -> "Omicron.sort_closure"))
     | Some _ -> assert false
     | _ -> sort_closure (push_var v env) sort)
  | _ ->
    extract_sort env sort >>= fun sort ->
    closure env sort.sort_kind sort (free_sort sort) >>= fun (cn, array) ->
    ok_sort (StConstant (cn, array))


and term_closure : type a. env -> a Omega.term -> a term Result.t =
  fun env term ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "term_closure")
    ~body:(fun fmt -> fmt "%a" Omega.pp_term term);*)
  match term.Omega.term_desc with
  | TmLambdaSort (s, term) ->
    extract_symbol env s >>= fun s ->
    (match pop_argument env with
     | Some (Sort st, env) ->
       (match equal_kind s.sym_kind st.sort_kind with
        | Eq -> term_closure (bind_sym s st env) term
        | _ -> failure (fun _ -> "Omicron.term_closure"))
     | Some _ -> assert false
     | _ -> term_closure (push_sym s env) term)
  | TmLambdaTerm (v, term) ->
    extract_variable env v >>= fun v ->
    (match pop_argument env with
     | Some (Term tm, env) ->
       (match equal_kind v.var_kind tm.term_kind with
        | Eq -> term_closure (bind_var v tm env) term
        | _ -> failure (fun _ -> "Omicron.term_closure"))
     | Some _ -> assert false
     | _ -> term_closure (push_var v env) term)
  | _ ->
    extract_term env term >>= fun term ->
    closure env term.term_sort term (free_term term) >>= fun (cn, array) ->
    ok_term (TmConstant (cn, array))


and extract_sort_lambdas  : type a. env -> a Omega.sort -> (a sort * sym_or_var list) Result.t =
  let rec aux : type a. env -> a Omega.sort -> sym_or_var list -> (a sort * sym_or_var list) Result.t =
    fun env sort list ->
      match sort.Omega.sort_desc with
      | StLambdaSort (s, sort) ->
        extract_symbol env s >>= fun s ->
        aux env sort (Sym s :: list)
      | StLambdaTerm (v, sort) ->
        extract_variable env v >>= fun v ->
        aux env sort (Var v :: list)
      | _ ->
        extract_sort env sort >>= fun sort ->
        Ok (sort, List.rev list)
  in
  fun env sort -> aux env sort []


and extract_term_lambdas : type a. env -> a Omega.term -> (a term * sym_or_var list) Result.t =
  let rec aux : type a. env -> a Omega.term -> sym_or_var list -> (a term * sym_or_var list) Result.t =
    fun env term list ->
      match term.Omega.term_desc with
      | TmLambdaSort (s, term) ->
        extract_symbol env s >>= fun s ->
        aux env term (Sym s :: list)
      | TmLambdaTerm (v, term) ->
        extract_variable env v >>= fun v ->
        aux env term (Var v :: list)
      | _ ->
        extract_term env term >>= fun term ->
        Ok (term, List.rev list)
  in
  fun env term -> aux env term []

(*
and check_sort_lambdas : type a. env -> sym_or_var list -> a Omega.sort -> a sort Result.t =
  fun env list sort ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "check_sort_lambdas")
    ~body:(fun fmt -> fmt "[@[%a]@]@\n%a"
              (Format.pp_print_list pp_sym_or_var) list Omega.pp_sort sort);*)
  match sort.Omega.sort_desc with
  | Omega.StLambdaSort (s, st) ->
    extract_symbol env s >>= fun s ->
    (match list with
     | Sym s' :: list when equal_symbol_name_kind s s' ->
       check_sort_lambdas env list st
     | _ -> failure (fun _ -> "Omicron.check_lambda_sort"))
  | Omega.StLambdaTerm (v, st) ->
    extract_variable env v >>= fun v ->
    (match list with
     | Var v' :: list when equal_variable_name_kind v v' ->
       check_sort_lambdas env list st
     | _ -> failure (fun _ -> "Omicron.check_lambda_sort"))
  |  _ ->
    (match list with
     | [] -> extract_sort env sort
     | _ -> failure (fun _ -> "Omicron.check_lambda_sort"))


and check_term_lambdas : type a. env -> sym_or_var list -> a Omega.term -> a term Result.t =
  fun env list term ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "check_term_lambdas")
    ~body:(fun fmt -> fmt "[@[%a]@]@\n%a"
              (Format.pp_print_list pp_sym_or_var) list Omega.pp_term term);*)
  match term.Omega.term_desc with
  | Omega.TmLambdaSort (s, tm) ->
    extract_symbol env s >>= fun s ->
    (match list with
     | Sym s' :: list when equal_symbol_name_kind s s' ->
       check_term_lambdas env list tm
     | _ -> failure (fun _ -> "Omicron.check_lambda_term"))
  | Omega.TmLambdaTerm (v, tm) ->
    extract_variable env v >>= fun v ->
    (match list with
     | Var v' :: list when equal_variable_name_kind v v' ->
       check_term_lambdas env list tm
     | _ -> failure (fun _ -> "Omicron.check_lambda_term"))
  |  _ ->
    (match list with
     | [] -> extract_term env term
     | _ -> failure (fun _ -> "Omicron.check_lambda_term"))
*)

and extract_symbol : type a. env -> a Omega.sym -> a sym Result.t =
  fun env s ->
  extract_kind env s.sym_kind >>= fun sym_kind ->
  Ok (mk_symbol s.Omega.sym_name sym_kind)


and extract_variable : type a. env -> a Omega.var -> a var Result.t =
  fun env v ->
  extract_kind env v.Omega.var_kind >>= fun var_kind ->
  extract_sort env v.Omega.var_sort >>= fun var_sort ->
  Ok (mk_variable v.Omega.var_name var_kind var_sort)


and extract_kind : type a. env -> a Omega.kind -> a kind Result.t =
  fun env kind ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_kind")
    ~body:(fun fmt -> fmt "%a" Omega.pp_kind kind);*)
  match kind.Omega.kind_desc with
  | Omega.KdProp -> Ok mk_kind_prop
  | Omega.KdSet  -> Ok mk_kind_set
  | Omega.KdArrowSort (s, kd) ->
    extract_symbol env s >>= fun s ->
    extract_kind env kd >>= fun kd ->
    Ok (mk_kind_arrow_sort s kd)
  | Omega.KdArrowTerm (v, kd) ->
    extract_variable env v >>= fun v ->
    extract_kind env kd >>= fun kd ->
    Ok (mk_kind_arrow_term v kd)


and extract_sort : type a. env -> a Omega.sort -> a sort Result.t =
  fun env sort ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_sort")
    ~body:(fun fmt -> fmt "%a" Omega.pp_sort sort);*)
  match sort.Omega.sort_desc with
  | Omega.StTrue -> ok_sort StTrue
  | Omega.StFalse -> ok_sort StFalse
  | Omega.StBool -> ok_sort StBool
  | Omega.StInt -> ok_sort StInt
  | Omega.StFloat -> ok_sort StFloat
  | Omega.StArray st ->
    extract_sort env st >>= fun st ->
    ok_sort (StArray st)
  | Omega.StSymbol (s, array) ->
    extract_symbol env s >>= fun s ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_sort (StSymbol (s, array))
  | Omega.StLambdaSort _ -> sort_closure env sort
  | Omega.StLambdaTerm _ -> sort_closure env sort
  | Omega.StApplySort (fn, st) ->
    extract_sort env st >>= fun st ->
    extract_sort (push_sort st env) fn
  | Omega.StApplyTerm (fn, tm) ->
    extract_term env tm >>= fun tm ->
    extract_sort (push_term tm env) fn
  | Omega.StProductSort (s, st) ->
    extract_symbol env s >>= fun s ->
    extract_sort env st >>= fun st ->
    ok_sort (StProductSort (s, st))
  | Omega.StProductTerm (v, st) ->
    extract_variable env v >>= fun v ->
    extract_sort env st >>= fun st ->
    ok_sort (StProductTerm (v, st))
  | Omega.StConstant (cn, array) ->
    extract_kind env cn.Omega.cnst_type >>= fun cnst_type ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    (match cn.Omega.cnst_body with
     | None ->
       Ok (Array.of_list (snd (get_arrows cnst_type)), None)
     | Some body ->
       extract_sort_lambdas env body >>= fun (body, prms) ->
       Ok (Array.of_list prms, Some body))
    >>= fun (cnst_prms, cnst_body) ->
    (*Result.Option.map (check_sort_lambdas env prms) cn.Omega.cnst_body >>= fun cnst_body ->*)
    ok_sort (StConstant (mk_constant cn.Omega.cnst_ident cnst_prms cnst_type cnst_body, array))
  | Omega.StInductive (iv, array) ->
    extract_inductive env iv >>= fun iv ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_sort (StInductive (iv, array))
  | Omega.StPrimitive (pm, kd, array) ->
    extract_kind env kd >>= fun kd ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_sort (StPrimitive (pm, kd, array))
  | Omega.StCase (cs, tm, array) ->
    extract_case_sort env cs array >>= fun cs ->
    extract_term env tm >>= fun tm ->
    ok_sort (StCase (cs, tm))


and extract_term : type a. env -> a Omega.term -> a term Result.t =
  fun env term ->
  (*Log.Verbose.debug
    ~head:(fun fmt -> fmt "extract_term")
    ~body:(fun fmt -> fmt "%a" Omega.pp_term term);*)
  match term.term_desc with
  | Omega.TmTrue -> ok_term TmTrue
  | Omega.TmBool bool -> ok_term (TmBool bool)
  | Omega.TmInt int -> ok_term (TmInt int)
  | Omega.TmFloat float -> ok_term (TmFloat float)
  | Omega.TmArray (array, tm) ->
    Result.Array.map (extract_term env) array >>= fun array ->
    extract_term env tm >>= fun tm ->
    ok_term (TmArray (array, tm))
  | Omega.TmVariable (v, array) ->
    extract_variable env v >>= fun v ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_term (TmVariable (v, array))
  | Omega.TmLambdaSort _ -> term_closure env term
  | Omega.TmLambdaTerm _ -> term_closure env term
  | Omega.TmApplySort (fn, st) ->
    extract_sort env st >>= fun st ->
    extract_term (push_sort st env) fn
  | Omega.TmApplyTerm (fn, tm) ->
    extract_term env tm >>= fun tm ->
    extract_term (push_term tm env) fn
  | Omega.TmConstant (cn, array) ->
    extract_sort env cn.Omega.cnst_type >>= fun cnst_type ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    (match cn.Omega.cnst_body with
     | None ->
       Ok (Array.of_list (snd (get_products cnst_type)), None)
     | Some body ->
       extract_term_lambdas env body >>= fun (body, prms) ->
       Ok (Array.of_list prms, Some body))
    >>= fun (cnst_prms, cnst_body) ->
    (*Result.Option.map (check_term_lambdas env prms) cn.Omega.cnst_body >>= fun cnst_body ->*)
    ok_term (TmConstant (mk_constant cn.Omega.cnst_ident cnst_prms cnst_type cnst_body, array))
  | Omega.TmConstruct (iv, int, array) ->
    extract_inductive env iv >>= fun iv ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_term (TmConstruct (iv, int, array))
  | Omega.TmProject (pj, tm) ->
    extract_projection env pj >>= fun pj ->
    extract_term env tm >>= fun tm ->
    ok_term (TmProject (pj, tm))
  | Omega.TmPrimitive (pm, st, array) ->
    extract_sort env st >>= fun st ->
    Result.Array.map (extract_sort_or_term env) array >>= fun array ->
    ok_term (TmPrimitive (pm, st, array))
  | Omega.TmCase (cs, tm, array) ->
    extract_case_term env cs array >>= fun cs ->
    extract_term env tm >>= fun tm ->
    ok_term (TmCase (cs, tm))


and extract_sort_or_term env sort_or_term =
  match sort_or_term with
  | Omega.Sort st -> extract_sort env st >>= fun st -> Ok (Sort st)
  | Omega.Term tm -> extract_term env tm >>= fun tm -> Ok (Term tm)


and extract_inductive : type a. env -> (a Omega.inductive * int) -> (a inductive * int) Result.t =
  fun env (Omega.{ indv_ident; indv_body; _ }, int) ->
  let string = ident_to_string indv_ident in
  match find_ind string env with
  | Some (AnyInductive indv') ->
    (match
       equal_witness
         (Omega.witness indv_body.mind_bodies.(int).oind_kind)
         (witness indv'.indv_body.mind_bodies.(int).oind_kind)
     with
     | Eq -> Ok (indv', int)
     | Nq -> assert false)
  | None ->
    extract_dummy_mutual_inductive env indv_body >>= fun mind ->
    let indv = mk_inductive indv_ident mind in
    let env = add_ind indv env in
    extract_mutual_inductive env indv_body >>= fun mind ->
    indv.indv_body <- mind;
    Log.Verbose.debug
      ~head:(fun fmt -> fmt "extract_inductive")
      ~body:(fun fmt -> fmt "%a" pp_inductive indv);
    Ok (indv, int)


and extract_dummy_mutual_inductive : type a. env -> a Omega.mutual_inductive -> a mutual_inductive Result.t =
  fun env Omega.{ mind_npars; mind_bodies; _ } ->
  Result.Array.map (extract_dummy_one_inductive env) mind_bodies >>= fun mind_bodies ->
  Ok (mk_mutual_inductive mind_npars mind_bodies)


and extract_dummy_one_inductive : type a. env -> a Omega.one_inductive -> a one_inductive Result.t =
  fun env Omega.{ oind_name; oind_kind; _ } ->
  extract_kind env oind_kind >>= fun oind_kind ->
  Ok (mk_one_inductive oind_name oind_kind [||])


and extract_mutual_inductive : type a. env -> a Omega.mutual_inductive -> a mutual_inductive Result.t =
  fun env Omega.{ mind_npars; mind_bodies; _ } ->
  Result.Array.map (extract_one_inductive env) mind_bodies >>= fun mind_bodies ->
  Ok (mk_mutual_inductive mind_npars mind_bodies)


and extract_one_inductive : type a. env -> a Omega.one_inductive -> a one_inductive Result.t =
  fun env Omega.{ oind_name; oind_kind; oind_ctors; _ } ->
  extract_kind env oind_kind >>= fun oind_kind ->
  Result.Array.map (extract_constructor env) oind_ctors >>= fun oind_ctors ->
  Ok (mk_one_inductive oind_name oind_kind oind_ctors)


and extract_constructor : type a. env -> a Omega.constructor -> a constructor Result.t =
  fun env Omega.{ ctor_name; ctor_kind; ctor_sort; ctor_nargs; _ } ->
  extract_kind env ctor_kind >>= fun ctor_kind ->
  extract_sort env ctor_sort >>= fun ctor_sort ->
  Ok (mk_constructor ctor_name ctor_kind ctor_sort ctor_nargs)


and extract_projection : type a b. env -> (a,b) Omega.projection -> (a,b) projection Result.t =
  fun env { proj_indv; proj_name; proj_sort; proj_indx; _ } ->
  extract_inductive env proj_indv >>= fun proj_indv ->
  extract_sort env proj_sort >>= fun proj_sort ->
  Ok (mk_projection proj_indv proj_name proj_sort proj_indx)


and extract_case_sort :
  type a b. env -> (a,b Omega.kind) Omega.case -> b Omega.sort array -> (a,b kind,b sort) case Result.t =
  fun env { case_nargs; case_indv; case_type; _ } array ->
  extract_inductive env case_indv >>= fun case_indv ->
  extract_kind env case_type >>= fun case_type ->
  extract_branches (extract_sort_lambdas env) case_nargs array >>= fun array ->
  Ok (mk_case case_indv case_type array)


and extract_case_term :
  type a b. env -> (a,b Omega.sort) Omega.case -> b Omega.term array -> (a,b sort,b term) case Result.t =
  fun env { case_nargs; case_indv; case_type; _ } array ->
  extract_inductive env case_indv >>= fun case_indv ->
  extract_sort env case_type >>= fun case_type ->
  extract_branches (extract_term_lambdas env) case_nargs array >>= fun array ->
  Ok (mk_case case_indv case_type array)


and extract_branches :
  type a b. (a -> (b * sym_or_var list) Result.t) -> int array -> a array -> b branch array Result.t =
  fun f nargs array ->
  Result.Array.map f array >>= fun array ->
  let array = Array.map (fun (desc, list) -> mk_branch (Array.of_list list) desc) array in
  if Array.for_all2 (fun int bnch -> Array.length bnch.bnch_prms = int) nargs array
  then Ok array
  else failure (fun _ -> "Omicron.extract_branches")


let extract_inductive : type a. (a Omega.inductive * int) -> (a inductive * int) Result.t =
  fun indv ->
  extract_inductive (create 17) indv


let extract_constant :
  type a. (a Omega.sort,a Omega.term) Omega.constant -> (a sort,a term) constant Result.t =
  fun cn ->
  let env = create 17 in
  extract_sort env cn.Omega.cnst_type >>= fun cnst_type ->
  (match cn.Omega.cnst_body with
   | None ->
     Ok (Array.of_list (snd (get_products cnst_type)), None)
   | Some body ->
     extract_term_lambdas env body >>= fun (body, prms) ->
     Ok (Array.of_list prms, Some body))
  >>= fun (cnst_prms, cnst_body) ->
  (*Result.Option.map (check_term_lambdas env prms) cn.Omega.cnst_body >>= fun cnst_body ->*)
  Ok (mk_constant cn.Omega.cnst_ident cnst_prms cnst_type cnst_body)

