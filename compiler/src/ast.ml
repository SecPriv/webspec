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

module Log = Logger.Default
    (struct
      let name = "ast"
    end)

type prop = Utils.prop
type set  = Utils.set

type _ kind = KindProp : prop kind | KindSet : set kind

type 'a sort = {
  sort_hash : int;
  sort_desc : 'a sort_desc;
}

and _ sort_desc =
  | SortProp : prop sort_desc
  | SortBool : set sort_desc
  | SortInt : set sort_desc
  | SortSymbol : string -> set sort_desc
  | SortArray  : set sort -> set sort_desc
  | SortDatatype : datatype * set sort list -> set sort_desc
  | SortDefn : sortdefn * set sort list -> set sort_desc

and sortdefn = {
  sdef_hash : int;
  sdef_name : string;
  sdef_prms : string list;
  sdef_desc : set sort;
}

and selector = {
  slct_hash : int;
  slct_name : string;
  slct_sort : set sort;
}

and constructor = {
  cnsr_hash : int;
  cnsr_name : string;
  selectors : selector list
}

and datatype = {
  dttp_hash : int;
  dttp_name : string;
  dttp_prms : string list;
  constructors : constructor list;
}

type var = {
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

and 'a term = {
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

and 'a case = {
  case_hash : int;
  case_name : string;
  case_vars : var list;
  case_desc : 'a term;
}

and 'a fundecl = {
  fdec_hash : int;
  fdec_name : string;
  fdec_prms : string list;
  fdec_vars : set sort list;
  fdec_desc : 'a sort;
}

and 'a fundefn = {
  fdef_hash : int;
  fdef_name : string;
  fdef_prms : string list;
  fdef_vars : var list;
  fdef_desc : 'a term;
}

type relation = {
  rela_hash : int;
  rela_name : string;
  rela_prms : set sort list;
}

type rule = {
  rule_hash : int;
  rule_name : string;
  rule_rela : string;
  rule_vars : var list;
  rule_desc : prop term;
}

type t =
  | Sort      of sortdefn
  | Datatype  of datatype
  | Function  of set fundefn
  | Predicate of prop fundefn
  | Relation  of relation
  | Query     of relation
  | Rule      of rule


let equal t1 t2 = t1 == t2 || t1 = t2

let kind : type a. a sort -> a kind =
  fun s ->
  match s.sort_desc with
  | SortProp -> KindProp
  | SortBool -> KindSet
  | SortInt -> KindSet
  | SortSymbol _ -> KindSet
  | SortArray _ -> KindSet
  | SortDatatype (_, _) -> KindSet
  | SortDefn (_, _) -> KindSet

type (_,_) eq = Eq : ('a,'a) eq | Nq : ('a,'b) eq

let _check : type a b. a sort -> b sort -> (a,b) eq =
  fun s1 s2 ->
  match kind s1, kind s2 with
  | KindProp, KindProp -> Eq
  | KindProp, KindSet -> Nq
  | KindSet,  KindProp -> Nq
  | KindSet,  KindSet -> Eq

let sort_list_hash list = List.map (fun s -> s.sort_hash) list
let var_list_hash  list = List.map (fun v -> v.var_hash)  list
let term_list_hash list = List.map (fun t -> t.term_hash) list
let case_list_hash list = List.map (fun c -> c.case_hash) list

let mk_sort : type a. a sort_desc -> a sort =
  fun sort_desc ->
  let sort_hash =
    match sort_desc with
    | SortProp -> Hashtbl.hash "SortProp"
    | SortBool -> Hashtbl.hash "SortBool"
    | SortInt -> Hashtbl.hash "SortInt"
    | SortSymbol string -> Hashtbl.hash ("SortSymbol", string)
    | SortArray s -> Hashtbl.hash ("SortArray", s.sort_hash)
    | SortDatatype (d, list) -> Hashtbl.hash ("SortDatatype", d.dttp_hash, sort_list_hash list)
    | SortDefn (sdef, list) -> Hashtbl.hash ("SortDefn", sdef.sdef_hash, sort_list_hash list)
  in
  { sort_hash; sort_desc }

let mk_sort_prop          = mk_sort SortProp
let mk_sort_bool          = mk_sort SortBool
let mk_sort_int           = mk_sort SortInt
let mk_sort_symbol string = mk_sort (SortSymbol string)
let mk_sort_array       s = mk_sort (SortArray s)
let mk_sort_datatype  d l = mk_sort (SortDatatype (d, l))
let mk_sort_defn   sdef l = mk_sort (SortDefn (sdef, l))

let mk_selector slct_name slct_sort =
  let slct_hash = Hashtbl.hash (slct_name, slct_sort.sort_hash) in
  { slct_hash; slct_name; slct_sort }

let mk_constructor cnsr_name selectors =
  let cnsr_hash =
    Hashtbl.hash (cnsr_name, List.map (fun s -> s.slct_hash) selectors)
  in
  { cnsr_hash; cnsr_name; selectors }

let mk_datatype dttp_name dttp_prms constructors =
  let dttp_hash =
    Hashtbl.hash (dttp_name, dttp_prms, List.map (fun c -> c.cnsr_hash) constructors)
  in
  { dttp_hash; dttp_name; dttp_prms; constructors }

let mk_sortdefn sdef_name sdef_prms sdef_desc =
  let sdef_hash =
    Hashtbl.hash
      (sdef_name, sdef_prms, sdef_desc.sort_hash)
  in
  { sdef_hash; sdef_name; sdef_prms; sdef_desc }

let merge l1 l2 = List.sort_uniq compare (List.merge compare l1 l2)
let fold_merge list = List.fold_left merge [] list
let remove v l = List.filter ((<>) v) l
let fold_remove vars free = List.fold_left (fun free v -> remove v free) free vars

let rec subst_prms : type a. set sort Utils.StringMap.t -> a sort -> a sort =
  fun map sort ->
  match sort.sort_desc with
  | SortProp -> sort
  | SortBool -> sort
  | SortInt -> sort
  | SortSymbol string ->
    (match Utils.StringMap.find_opt string map with
     | Some sort -> sort
     | None -> sort)
  | SortArray s ->
    let s = subst_prms map s in
    mk_sort_array s
  | SortDatatype (dttp, list)  ->
    let list = List.map (subst_prms map) list in
    let map =
      List.fold_left
        (fun map string -> Utils.StringMap.remove string map)
        map dttp.dttp_prms in
    if Utils.StringMap.is_empty map then sort
    else
      mk_sort_datatype
        (mk_datatype dttp.dttp_name dttp.dttp_prms
           (List.map
              (fun cnsr ->
                 mk_constructor cnsr.cnsr_name
                   (List.map
                      (fun slct ->
                         mk_selector slct.slct_name
                           (subst_prms map slct.slct_sort))
                      cnsr.selectors))
              dttp.constructors))
        list
  | SortDefn (sdef, list) ->
    let list = List.map (subst_prms map) list in
    let map =
      List.fold_left
        (fun map string -> Utils.StringMap.remove string map)
        map sdef.sdef_prms in
    if Utils.StringMap.is_empty map then sort
    else
      mk_sort_defn
        (mk_sortdefn sdef.sdef_name sdef.sdef_prms
           (subst_prms map sdef.sdef_desc))
        list

let subst_prms sort prms sorts =
  let map =
    List.fold_left2
      (fun map string sort -> Utils.StringMap.add string sort map)
      Utils.StringMap.empty prms sorts
  in
  if Utils.StringMap.is_empty map then sort
  else subst_prms map sort

let term_hash_sort_free : type a. a term_desc -> int * a sort * var list =
  fun term_desc ->
  match term_desc with
  | TermTrue  -> Hashtbl.hash "TermTrue", mk_sort_prop, []
  | TermFalse -> Hashtbl.hash "TermFalse", mk_sort_prop, []
  | TermBool _ -> Hashtbl.hash "TermBool", mk_sort_bool, []
  | TermInt int -> Hashtbl.hash ("TermInt", int), mk_sort_int, []

  | TermVar v ->
    Hashtbl.hash ("TermVar", v.var_hash), v.var_sort, [v]
  | TermLet (v, t1, t2) ->
    Hashtbl.hash ("TermLet", v.var_hash, t1.term_hash, t2.term_hash),
    t2.term_sort,
    merge t1.term_free (remove v t2.term_free)
  | TermExists  (v, f) ->
    Hashtbl.hash ("TermExists", v.var_hash, f.term_hash),
    mk_sort_prop,
    remove v f.term_free
  | TermForall  (v, f) ->
    Hashtbl.hash ("TermForall", v.var_hash, f.term_hash),
    mk_sort_prop,
    remove v f.term_free
  | TermMatch (t, list) ->
    Hashtbl.hash ("TermMatch", t.term_hash, case_list_hash list),
    (List.hd list).case_desc.term_sort,
    fold_merge
      (List.map (fun cs -> fold_remove cs.case_vars cs.case_desc.term_free) list)
    |> merge t.term_free
  | TermIte (f, t1, t2) ->
    Hashtbl.hash ("TermIte", f.term_hash, t1.term_hash, t2.term_hash),
    t1.term_sort,
    merge f.term_free (merge t1.term_free t2.term_free)

  | TermVariadic (v, list) ->
    (match v with
     | Distinct ->
       Hashtbl.hash ("TermDistinct", List.map (fun t -> t.term_hash) list),
       mk_sort_prop, fold_merge (List.map (fun t -> t.term_free) list))

  | TermUnop (u, t) ->
    (match u with
     | Classic -> Hashtbl.hash ("TermClassic", t.term_hash), mk_sort_bool, t.term_free
     | Not -> Hashtbl.hash ("TermNot", t.term_hash), mk_sort_prop, t.term_free
     | Succ -> Hashtbl.hash ("TermSucc", t.term_hash), mk_sort_int, t.term_free)
  | TermBnop (b, t1, t2) ->
    (match b with
     | Imply ->
       Hashtbl.hash ("TermImply", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | And ->
       Hashtbl.hash ("TermAnd", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Or ->
       Hashtbl.hash ("TermOr", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Equal ->
       Hashtbl.hash ("TermEqual", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Le ->
       Hashtbl.hash ("TermLe", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Lt ->
       Hashtbl.hash ("TermLt", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Ge ->
       Hashtbl.hash ("TermGe", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Gt ->
       Hashtbl.hash ("TermGt", t1.term_hash, t2.term_hash),
       mk_sort_prop, merge t1.term_free t2.term_free
     | Add ->
       Hashtbl.hash ("TermAdd", t1.term_hash, t2.term_hash),
       mk_sort_int, merge t1.term_free t2.term_free
     | Sub ->
       Hashtbl.hash ("TermSub", t1.term_hash, t2.term_hash),
       mk_sort_int, merge t1.term_free t2.term_free)
  | TermDecl (fdec, slist, list) ->
    Hashtbl.hash ("TermDecl", fdec.fdec_hash, sort_list_hash slist, term_list_hash list),
    subst_prms fdec.fdec_desc fdec.fdec_prms slist,
    fold_merge (List.map (fun t -> t.term_free) list)
  | TermDefn (fdef, slist, list) ->
    Hashtbl.hash ("TermDefn", fdef.fdef_hash, sort_list_hash slist, term_list_hash list),
    subst_prms fdef.fdef_desc.term_sort fdef.fdef_prms slist,
    fold_merge (List.map (fun t -> t.term_free) list)

  | TermConstruct (d, l, int, list) ->
    Hashtbl.hash ("TermConstruct", d.dttp_hash, sort_list_hash l, int, term_list_hash list),
    mk_sort_datatype d l,
    fold_merge (List.map (fun t -> t.term_free) list)
  | TermSelect (d, l, int1, int2, t) ->
    Hashtbl.hash ("TermSelect", d.dttp_hash, sort_list_hash l, int1, int2, t.term_hash),
    subst_prms
      (List.nth (List.nth d.constructors int1).selectors int2).slct_sort
      d.dttp_prms l,
    t.term_free

  | ArrayConst (s, e) ->
    Hashtbl.hash
      ("ArrayConst", s.sort_hash, e.term_hash),
    mk_sort (SortArray s),
    e.term_free
  | ArrayRead (s, a, i) ->
    Hashtbl.hash
      ("ArrayRead", s.sort_hash, a.term_hash, i.term_hash),
    s,
    merge a.term_free i.term_free
  | ArrayWrite (s, a, i, e) ->
    Hashtbl.hash
      ("ArrayWrite", s.sort_hash, a.term_hash, i.term_hash, e.term_hash),
    a.term_sort,
    merge a.term_free (merge i.term_free e.term_free)
  | ArrayMap (f, slist, list, a) ->
    Hashtbl.hash
      ("ArrayMap", f.fdef_hash, sort_list_hash slist, term_list_hash list, a.term_hash),
    mk_sort (SortArray (subst_prms f.fdef_desc.term_sort f.fdef_prms slist)),
    a.term_free
  | ArrayDistinct (s, a) ->
    Hashtbl.hash
      ("ArrayDistinct", s.sort_hash, a.term_hash),
    mk_sort_prop,
    a.term_free

let mk_variable var_name var_sort =
  let var_hash = Hashtbl.hash (var_name, var_sort.sort_hash) in
  { var_hash; var_name; var_sort }

let mk_case case_name case_vars case_desc =
  let case_hash =
    Hashtbl.hash
      (case_name, var_list_hash case_vars, case_desc.term_hash)
  in
  { case_hash; case_name; case_vars; case_desc }

let mk_term_true =
  let term_desc = TermTrue in
  let term_hash, term_sort, term_free = term_hash_sort_free term_desc in
  { term_hash; term_sort; term_desc; term_free }

let mk_term_false =
  let term_desc = TermFalse in
  let term_hash, term_sort, term_free = term_hash_sort_free term_desc in
  { term_hash; term_sort; term_desc; term_free }

let mk_term_bool bool =
  let term_desc = TermBool bool in
  let term_hash, term_sort, term_free = term_hash_sort_free term_desc in
  { term_hash; term_sort; term_desc; term_free }

let mk_term_int int =
  let term_desc = TermInt int in
  let term_hash, term_sort, term_free = term_hash_sort_free term_desc in
  { term_hash; term_sort; term_desc; term_free }

let rec mk_term : type a. a term_desc -> a term =
  fun term_desc ->
  let term_hash, term_sort, term_free = term_hash_sort_free term_desc in
  match term_desc with

  | TermUnop (Not, f) ->
    (match f.term_desc with
     | TermTrue -> mk_term_false
     | TermFalse -> mk_term_true
     | TermUnop (Not, f) -> f
     | _ -> { term_hash; term_sort; term_desc; term_free })

  | TermBnop (Imply, f1, f2) ->
    (match f1.term_desc with
     | TermTrue -> f2
     | TermFalse -> mk_term_true
     | _ ->
       match f2.term_desc with
       | TermTrue -> mk_term_true
       | TermFalse -> mk_term (TermUnop (Not, f1))
       | TermBnop (Imply, f21, f22) ->
         mk_term (TermBnop (Imply, mk_term (TermBnop (And, f1, f21)), f22))
       | _ -> { term_hash; term_sort; term_desc; term_free })

  | TermBnop (And, f1, f2) ->
    (match f1.term_desc with
     | TermTrue -> f2
     | TermFalse -> mk_term_false
     | _ ->
       match f2.term_desc with
       | TermTrue -> f1
       | TermFalse -> mk_term_false
       | _ -> { term_hash; term_sort; term_desc; term_free })

  | TermBnop (Or, f1, f2) ->
    (match f1.term_desc with
     | TermTrue -> mk_term_true
     | TermFalse -> f2
     | _ ->
       match f2.term_desc with
       | TermTrue -> mk_term_true
       | TermFalse -> f1
       | _ -> { term_hash; term_sort; term_desc; term_free })

  | TermBnop (Equal, t1, t2) ->
    (if equal t1 t2 then mk_term_true
     else
       match t1.term_desc, t2.term_desc with
       | TermInt int1, TermInt int2 ->
         if int1 = int2 then mk_term_true else mk_term_false
       | TermMatch (t, list), _ ->
         let list =
           List.map
             (fun cs ->
                mk_case
                  cs.case_name cs.case_vars
                  (mk_term (TermBnop (Equal, cs.case_desc, t2))))
             list
         in
         mk_term (TermMatch (t, list))
       | _, TermMatch (t, list) ->
         let list =
           List.map
             (fun cs ->
                mk_case
                  cs.case_name cs.case_vars
                  (mk_term (TermBnop (Equal, t1, cs.case_desc))))
             list
         in
         mk_term (TermMatch (t, list))
       | TermConstruct (d1, l1, int1, list1), TermConstruct (d2, l2, int2, list2) ->
         assert (equal d1 d2 && List.for_all2 equal l1 l2);
         if int1 <> int2 then mk_term_false
         else
           List.fold_right2
             (fun t1 t2 acc ->
                mk_term (TermBnop (And, mk_term (TermBnop (Equal, t1, t2)), acc)))
             list1 list2 mk_term_true
       | _, _ -> { term_hash; term_sort; term_desc; term_free })

  | TermIte (f, t1, t2) ->
    (match f.term_desc with
     | TermBool bool -> if bool then t1 else t2
     | TermUnop (Classic, f) ->
       (match f.term_desc with
        | TermTrue -> t1
        | TermFalse -> t2
        | _ -> { term_hash; term_sort; term_desc; term_free })
     | _ -> { term_hash; term_sort; term_desc; term_free })

  | TermSelect (d, l, int1, int2, t) ->
    (match t.term_desc with
     | TermConstruct (d', l', int, list) ->
       assert (int1 = int && d = d' && List.for_all2 (=) l l');
       List.nth list int2
     | _ -> { term_hash; term_sort; term_desc; term_free })

  | _ -> { term_hash; term_sort; term_desc; term_free }

let mk_term_var        v = mk_term (TermVar v)
let mk_term_let  v t1 t2 = mk_term (TermLet (v, t1, t2))
let mk_term_exists   v f = mk_term (TermExists (v, f))
let mk_term_forall   v f = mk_term (TermForall (v, f))
let mk_term_match t list = mk_term (TermMatch (t, list))
let mk_term_ite  f t1 t2 = mk_term (TermIte (f, t1, t2))

let mk_term_variadic v l = mk_term (TermVariadic (v, l))
let mk_term_unop u t     = mk_term (TermUnop (u, t))
let mk_term_bnop b t1 t2 = mk_term (TermBnop (b, t1, t2))
let mk_term_decl d sl tl = mk_term (TermDecl (d, sl, tl))
let mk_term_defn d sl tl = mk_term (TermDefn (d, sl, tl))

let mk_term_construct d l int list = mk_term (TermConstruct (d, l, int, list))
let mk_term_select d l int1 int2 t = mk_term (TermSelect (d, l, int1, int2, t))

let mk_array_const s t     = mk_term (ArrayConst (s, t))
let mk_array_read  s a i   = mk_term (ArrayRead (s, a, i))
let mk_array_write s a i e = mk_term (ArrayWrite (s, a, i, e))
let mk_array_map f sl tl a = mk_term (ArrayMap (f, sl, tl, a))
let mk_array_distinct s a  = mk_term (ArrayDistinct (s, a))

let mk_term_distinct l = mk_term_variadic Distinct l

let mk_term_classic f = mk_term_unop Classic f
let mk_term_not  f = mk_term_unop Not f
let mk_term_succ t = mk_term_unop Succ t

let mk_term_imply f1 f2 = mk_term_bnop Imply f1 f2
let mk_term_and   f1 f2 = mk_term_bnop And f1 f2
let mk_term_or    f1 f2 = mk_term_bnop Or f1 f2
let mk_term_equal t1 t2 = mk_term_bnop Equal t1 t2
let mk_term_lt    t1 t2 = mk_term_bnop Lt t1 t2
let mk_term_le    t1 t2 = mk_term_bnop Le t1 t2
let mk_term_gt    t1 t2 = mk_term_bnop Gt t1 t2
let mk_term_ge    t1 t2 = mk_term_bnop Ge t1 t2
let mk_term_add   t1 t2 = mk_term_bnop Add t1 t2
let mk_term_sub   t1 t2 = mk_term_bnop Sub t1 t2

let mk_fundecl fdec_name fdec_prms fdec_vars fdec_desc =
  let fdec_hash =
    Hashtbl.hash (fdec_name, fdec_prms, sort_list_hash fdec_vars, fdec_desc.sort_hash)
  in
  { fdec_hash; fdec_name; fdec_prms; fdec_vars; fdec_desc }

let mk_fundefn fdef_name fdef_prms fdef_vars fdef_desc =
  let fdef_hash =
    Hashtbl.hash (fdef_name, fdef_prms, var_list_hash fdef_vars, fdef_desc.term_hash)
  in
  { fdef_hash; fdef_name; fdef_prms; fdef_vars; fdef_desc }

let mk_relation rela_name rela_prms =
  let rela_hash = Hashtbl.hash (rela_name, sort_list_hash rela_prms) in
  { rela_hash; rela_name; rela_prms }

let mk_rule rule_name rule_rela rule_vars rule_desc =
  let rule_hash =
    Hashtbl.hash
      (rule_name, rule_rela, var_list_hash rule_vars, rule_desc.term_hash)
  in
  { rule_hash; rule_name; rule_rela; rule_vars; rule_desc }

