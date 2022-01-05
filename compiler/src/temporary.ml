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
      let name = "temporary"
    end)

let push, flush =
  let list = ref [] in
  (fun (t: Ast.t) -> list := t :: !list),
  (fun () -> let res = List.rev !list in list := []; res)

type env = {
  dttp_map : Ast.datatype StringHashtbl.t;
  rela_map : Ast.relation StringHashtbl.t;
  name_map : string StringHashtbl.t;
}

let create n = {
  dttp_map = StringHashtbl.create n;
  rela_map = StringHashtbl.create n;
  name_map = StringHashtbl.create n;
}

let add_dttp dttp env =
  assert (not (StringHashtbl.mem env.dttp_map dttp.Ast.dttp_name));
  StringHashtbl.add env.dttp_map dttp.Ast.dttp_name dttp;
  env

let replace_dttp dttp env =
  StringHashtbl.replace env.dttp_map dttp.Ast.dttp_name dttp

let find_dttp string env = StringHashtbl.find_opt env.dttp_map string

let add_rela rela env =
  assert (not (StringHashtbl.mem env.rela_map rela.Ast.rela_name));
  StringHashtbl.add env.rela_map rela.Ast.rela_name rela;
  env

let replace_rela rela env =
  StringHashtbl.replace env.rela_map rela.Ast.rela_name rela

let find_rela string env = StringHashtbl.find_opt env.rela_map string

let add_name string1 string2 env =
  assert (not (StringHashtbl.mem env.name_map string1));
  StringHashtbl.add env.name_map string1 string2

let find_name name env =
  let string = Name.to_string name in
  match StringHashtbl.find_opt env.name_map string with
  | None -> string
  | Some string -> string

let rela_name name = name

let relation_to_fundecl Ast.{ rela_name; rela_prms; _ } =
  Ast.(mk_fundecl rela_name [] rela_prms mk_sort_prop)

let name_anonymous nm =
  match nm with
  | Name.Anonymous -> Name.fresh ()
  | _ -> nm


let sym_to_sym : env -> set Omicron.sym -> string Result.t =
  fun env { sym_name; _ } ->
  match sym_name with
  | Anonymous -> failure (fun _ -> "Temporary.sym_to_sym")
  | nm -> Ok (find_name nm env)

let rec var_to_var : env -> set Omicron.var -> Ast.var Result.t =
  fun env { var_name; var_sort; _ } ->
  match name_anonymous var_name with
  | Anonymous -> failure (fun _ -> "Temporary.var_to_var")
  | Id int ->
    sort_to_sort env var_sort >>= fun sort ->
    Ok (Ast.mk_variable (Printf.sprintf "%s<%i>" (Ast_utils.sort_to_string sort) int) sort)
  | Name string ->
    sort_to_sort env var_sort >>= fun sort ->
    Ok (Ast.mk_variable string sort)


and sort_to_sort : type a. env -> a Omicron.sort -> a Ast.sort Result.t =
  fun env sort ->
  match sort.Omicron.sort_desc with
  | Omicron.StTrue -> Ok Ast.mk_sort_prop
  | Omicron.StFalse -> Ok Ast.mk_sort_prop
  | Omicron.StBool -> Ok Ast.mk_sort_bool
  | Omicron.StInt -> Ok Ast.mk_sort_int
  | Omicron.StFloat -> failure (fun _ -> "Temporary.sort_to_sort StFloat")
  | Omicron.StArray st ->
    sort_to_sort env st >>= fun st ->
    Ok (Ast.mk_sort_array st)
  | Omicron.StSymbol (s, array) ->
    (match Omicron.witness s.Omicron.sym_kind, array with
     | Set, [||] ->
       sym_to_sym env s >>= fun s ->
       Ok (Ast.mk_sort_symbol s)
     | _ -> failure (fun _ -> "Temporary.sort_to_sort StSymbol"))
  | Omicron.StProductSort (_, _) -> failure (fun _ -> "Temporary.sort_to_sort StProductSort")
  | Omicron.StProductTerm (_, _) -> failure (fun _ -> "Temporary.sort_to_sort StProductTerm")
  | Omicron.StConstant (cn, array) ->
    (match Omicron.(witness cn.cnst_type) with
     | Prop -> failure (fun _ -> "Temporary.sort_to_sort StConstant")
     | Set ->
       constant_to_sortdefn env cn >>= fun sdef ->
       filter_map_set_sorts env (Array.to_list array) >>= fun list ->
       Ok Ast.(mk_sort_defn sdef list))
  | Omicron.StInductive (indv, array) ->
    let oind = Omicron.get_one_inductive indv in
    (match Omicron.(witness oind.oind_kind) with
     | Prop -> Ok Ast.mk_sort_prop
     | Set ->
       match oind.Omicron.oind_name with
       | "nat" -> Ok Ast.mk_sort_int
       | "bool" -> Ok Ast.mk_sort_bool
       | "sumbool" -> assert false
       | _ ->
         inductive_to_datatype env indv >>= fun dttp ->
         filter_map_set_sorts env (Array.to_list array) >>= fun list ->
         Ok Ast.(mk_sort_datatype dttp list))
  | Omicron.StPrimitive (_, _, _) -> failure (fun _ -> "Temporary.sort_to_sort StPrimitive")
  | Omicron.StCase (_, _) -> failure (fun _ -> "Temporary.sort_to_sort StCase")


and sort_to_form : env -> prop Omicron.sort -> prop Ast.term Result.t =
  fun env sort ->
  match sort.Omicron.sort_desc with
  | Omicron.StTrue  -> Ok Ast.mk_term_true
  | Omicron.StFalse -> Ok Ast.mk_term_false
  | Omicron.StProductSort _ -> failure (fun _ -> "Temporary.sort_to_form StProductSort")
  | Omicron.StProductTerm (v, sort) ->
    (match Omicron.witness v.Omicron.var_kind with
     | Prop ->
       sort_to_form env sort >>= fun right ->
       sort_to_form env v.Omicron.var_sort >>= fun left ->
       Ok Ast.(mk_term_imply left right)
     | Set ->
       sort_to_form env sort >>= fun form ->
       var_to_var env v >>= fun v ->
       Ok Ast.(mk_term_forall v form))
  | Omicron.StConstant ({ cnst_ident; cnst_prms; cnst_body; _ }, array) ->
    let list = Array.to_list array in
    filter_map_set_sorts env list >>= fun sorts ->
    filter_map_set_terms env list >>= fun terms ->
    (match cnst_body with
     | None -> failure (fun _ -> "Temporary.sort_to_form StConstant")
     | Some sort ->
       filter_map_syms ~f:name_anonymous env (Array.to_list cnst_prms) >>= fun prms ->
       filter_map_vars ~f:name_anonymous env (Array.to_list cnst_prms) >>= fun vars ->
       sort_to_form env sort >>= fun form ->
       Ok Ast.(mk_term_defn (mk_fundefn (fst cnst_ident) prms vars form) sorts terms))
  | Omicron.StInductive (indv, array) ->
    (match Omicron.((get_one_inductive indv).oind_name) with
     | "eq" ->
       ensure_set_term env array.(1) >>= fun tm1 ->
       ensure_set_term env array.(2) >>= fun tm2 ->
       Ok Ast.(mk_term_equal tm1 tm2)
     | "and" ->
       ensure_prop_sort env array.(0) >>= fun tm1 ->
       ensure_prop_sort env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_and tm1 tm2)
     | "or" ->
       ensure_prop_sort env array.(0) >>= fun tm1 ->
       ensure_prop_sort env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_or tm1 tm2)
     | "False" -> Ok Ast.mk_term_false
     | "True"  -> Ok Ast.mk_term_true
     | _ ->
       inductive_to_relation env indv >>= fun rela ->
       filter_map_set_terms env (Array.to_list array) >>= fun list ->
       Ok Ast.(mk_term_decl (relation_to_fundecl rela) [] list))
  | Omicron.StPrimitive (pm, _, array) ->
    (match pm with
     | Primitive.True -> Ok Ast.mk_term_true
     | Primitive.False -> Ok Ast.mk_term_false
     | Primitive.Eq ->
       ensure_set_term env array.(1) >>= fun tm1 ->
       ensure_set_term env array.(2) >>= fun tm2 ->
       Ok Ast.(mk_term_equal tm1 tm2)
     | Primitive.Lt ->
       ensure_set_term env array.(0) >>= fun tm1 ->
       ensure_set_term env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_lt tm1 tm2)
     | Primitive.Le ->
       ensure_set_term env array.(0) >>= fun tm1 ->
       ensure_set_term env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_le tm1 tm2)
     | Primitive.Gt ->
       ensure_set_term env array.(0) >>= fun tm1 ->
       ensure_set_term env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_gt tm1 tm2)
     | Primitive.Ge ->
       ensure_set_term env array.(0) >>= fun tm1 ->
       ensure_set_term env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_ge tm1 tm2)
     | Primitive.And ->
       ensure_prop_sort env array.(0) >>= fun tm1 ->
       ensure_prop_sort env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_and tm1 tm2)
     | Primitive.Or ->
       ensure_prop_sort env array.(0) >>= fun tm1 ->
       ensure_prop_sort env array.(1) >>= fun tm2 ->
       Ok Ast.(mk_term_or tm1 tm2)
     | Primitive.Not ->
       ensure_prop_sort env array.(0) >>= fun tm ->
       Ok Ast.(mk_term_not tm)
     | Primitive.ArrayDistinct ->
       ensure_set_sort env array.(0) >>= fun st ->
       ensure_set_term env array.(1) >>= fun arr ->
       Ok Ast.(mk_array_distinct st arr))
  | Omicron.StCase (case, term) ->
    (match Omicron.(witness term.term_kind) with
     | Prop -> failure (fun _ -> "Temporary.sort_to_form StCase")
     | Set ->
       sort_case_to_cases env case >>= fun list ->
       term_to_term env term >>= fun term ->
       match Omicron.((get_one_inductive case.case_indv).oind_name), list with
       | "nat", [z; s] ->
         Ok Ast.(mk_term_ite
                   (mk_term_classic (mk_term_gt term (mk_term_int 0)))
                   (mk_term_let (List.hd s.case_vars) (mk_term_sub term (mk_term_int 1)) s.case_desc)
                   z.case_desc)
       | "bool", [t; e] ->
         Ok Ast.(mk_term_ite term t.case_desc e.case_desc)
       | "sumbool", [l; r] ->
         Ok Ast.(mk_term_ite term l.case_desc r.case_desc)
       | _ -> Ok Ast.(mk_term_match term list))
  | Omicron.StBool       -> failure (fun _ -> "Temporary.sort_to_form StBool")
  | Omicron.StInt        -> failure (fun _ -> "Temporary.sort_to_form StInt")
  | Omicron.StFloat      -> failure (fun _ -> "Temporary.sort_to_form StFloat")
  | Omicron.StArray _    -> failure (fun _ -> "Temporary.sort_to_form StArray")
  | Omicron.StSymbol _   -> (* TODO *) failure (fun _ -> "Temporary.sort_to_form StSymbol")


and term_to_term : type a. env -> a Omicron.term -> a Ast.term Result.t =
  fun env term ->
  match term.Omicron.term_desc with
  | Omicron.TmBool bool -> Ok Ast.(mk_term_bool bool)
  | Omicron.TmInt  int  -> Ok Ast.(mk_term_int  int)
  | Omicron.TmVariable (v, array) ->
    if Array.length array = 0 then
      match Omicron.witness v.Omicron.var_kind with
      | Prop -> failure (fun _ -> "Temporary.term_to_term TmVariable")
      | Set ->
        var_to_var env v >>= fun v ->
        Ok Ast.(mk_term_var v)
    else failure (fun _ -> "Temporary.term_to_term TmVariable")
  | Omicron.TmConstant (cn, array) ->
    (match cn.Omicron.cnst_ident with
     | "classic", _ ->
       ensure_prop_sort env array.(0) >>= fun form ->
       (match Omicron.(witness term.Omicron.term_kind) with
        | Prop -> Ok (form : a Ast.term)
        | Set  -> Ok Ast.(mk_term_classic form))
     | _ ->
       let list = Array.to_list array in
       filter_map_set_sorts env list >>= fun sorts ->
       filter_map_set_terms env list >>= fun terms ->
       (match cn.Omicron.cnst_body with
        | None ->
          constant_to_fundecl env cn >>= fun fdec ->
          Ok Ast.(mk_term_decl fdec sorts terms)
        | Some _ ->
          constant_to_fundefn env cn >>= fun fdef ->
          Ok Ast.(mk_term_defn fdef sorts terms)))
  | Omicron.TmConstruct (indv, int, array) ->
    let oind = Omicron.get_one_inductive indv in
    (match Omicron.(witness oind.oind_kind) with
     | Prop -> failure (fun _ -> "Temporary.term_to_term TmConstruct")
     | Set  ->
       let list = Array.to_list array in
       filter_map_set_sorts env list >>= fun sorts ->
       filter_map_set_terms env list >>= fun terms ->
       match oind.Omicron.oind_name, int with
       | "nat", 0 -> Ok Ast.(mk_term_int 0)
       | "nat", 1 -> Ok Ast.(mk_term_succ (List.hd terms))
       | "nat", _ -> assert false
       | "bool", 0 -> Ok Ast.(mk_term_bool true)
       | "bool", 1 -> Ok Ast.(mk_term_bool false)
       | "bool", _ -> assert false
       | "sumbool", _ -> assert false
       | _ ->
         inductive_to_datatype env indv >>= fun dttp ->
         Ok Ast.(mk_term_construct dttp sorts int terms))
  | Omicron.TmProject (proj, term) ->
    (match Omicron.(witness proj.proj_sort.sort_kind), Omicron.(witness term.term_kind) with
     | Set, Set ->
       term_to_term env term >>= fun term ->
       (match term.Ast.term_sort.Ast.sort_desc with
        | Ast.SortDatatype (dttp, list) ->
          Ok Ast.(mk_term_select dttp list 0 proj.Omicron.proj_indx term)
        | _ -> failure (fun _ -> "Temporary.term_to_term TmProject"))
     | _ -> failure (fun _ -> "Temporary.term_to_term TmProject"))
  | Omicron.TmPrimitive (pm, st, array) ->
    (match Omicron.witness st.Omicron.sort_kind, pm with
     | Set, Primitive.ArrayMake ->
       ensure_set_sort env array.(0) >>= fun st ->
       ensure_set_term env array.(1) >>= fun elt ->
       Ok Ast.(mk_array_const st elt)
     | Set, Primitive.ArrayGet ->
       ensure_set_sort env array.(0) >>= fun st ->
       ensure_set_term env array.(1) >>= fun arr ->
       ensure_set_term env array.(2) >>= fun idx ->
       Ok Ast.(mk_array_read st arr idx)
     | Set, Primitive.ArraySet ->
       ensure_set_sort env array.(0) >>= fun st ->
       ensure_set_term env array.(1) >>= fun arr ->
       ensure_set_term env array.(2) >>= fun idx ->
       ensure_set_term env array.(3) >>= fun elt ->
       Ok Ast.(mk_array_write st arr idx elt)
     | Set, Primitive.ArrayMap ->
       Omicron.get_products st |> snd |> (filter_map_syms env) >>= fun products ->
       add_name (List.nth products 0) "T" env;
       add_name (List.nth products 1) "U" env;
       ensure_set_sort env array.(0) >>= fun t ->
       ensure_set_sort env array.(1) >>= fun u ->
       ensure_set_term env array.(2) >>= fun f ->
       ensure_set_term env array.(3) >>= fun arr ->
       (match f.Ast.term_desc with
        | Ast.TermDefn ({ fdef_name; fdef_prms; fdef_vars; fdef_desc; _ }, slist, list) ->
          (* TODO: something less ugly *)
          let free = List.filter (fun v -> not (List.mem v fdef_vars)) fdef_desc.Ast.term_free in
          let f = Ast.mk_fundefn fdef_name (fdef_prms @ ["T"; "U"]) (fdef_vars @ free) fdef_desc in
          Ok Ast.(mk_array_map f (slist @ [t; u]) list arr)
        | _ -> failure (fun _ -> "Temporary.term_to_term TmPrimitive"))
     | Set, Primitive.Eqb ->
       ensure_set_term env array.(1) >>= fun tm1 ->
       ensure_set_term env array.(2) >>= fun tm2 ->
       Ok Ast.(mk_term_classic (mk_term_equal tm1 tm2))
     | _, _ -> failure (fun _ -> "Temporary.term_to_term TmPrimitive"))
  | Omicron.TmCase (case, term) ->
    (match Omicron.(witness term.term_kind) with
     | Prop -> failure (fun _ -> "Temporary.term_to_term TmCase")
     | Set ->
       match term.Omicron.term_desc with
       | Omicron.(TmConstant (cn, array)) when String.equal "classic" (fst cn.cnst_ident) ->
         ensure_prop_sort env array.(0) >>= fun form ->
         term_to_term env case.Omicron.case_branches.(0).Omicron.bnch_desc >>= fun t ->
         term_to_term env case.Omicron.case_branches.(1).Omicron.bnch_desc >>= fun e ->
         Ok Ast.(mk_term_ite (mk_term_classic form) t e)
       | _ ->
         term_case_to_cases env case >>= fun list ->
         term_to_term env term >>= fun term ->
         match Omicron.((get_one_inductive case.case_indv).oind_name), list with
         | "nat", [z; s] ->
           Ok Ast.(mk_term_ite
                     (mk_term_classic (mk_term_gt term (mk_term_int 0)))
                     (mk_term_let (List.hd s.case_vars) (mk_term_sub term (mk_term_int 1)) s.case_desc)
                     z.case_desc)
         | "bool", [t; e] ->
           Ok Ast.(mk_term_ite term t.case_desc e.case_desc)
         | "sumbool", [l; r] ->
           Ok Ast.(mk_term_ite term l.case_desc r.case_desc)
         | _ -> Ok Ast.(mk_term_match term list))
  | Omicron.TmTrue    -> failure (fun _ -> "Temporary.term_to_term TmTrue")
  | Omicron.TmFloat _ -> failure (fun _ -> "Temporary.term_to_term TmFloat")
  | Omicron.TmArray _ -> failure (fun _ -> "Temporary.term_to_term TmArray")


and constant_to_sortdefn :
  env -> (set Omicron.kind,set Omicron.sort) Omicron.constant -> Ast.sortdefn Result.t =
  fun env { cnst_ident; cnst_prms; cnst_body; _ } ->
  match cnst_body with
  | None -> failure (fun _ -> "Temporary.constant_to_sortdefn")
  | Some sort ->
    filter_map_syms ~f:name_anonymous env (Array.to_list cnst_prms) >>= fun prms ->
    sort_to_sort env sort >>= fun sort ->
    Ok Ast.(mk_sortdefn (fst cnst_ident) prms sort)


and constant_to_fundefn :
  type a. env -> (a Omicron.sort,a Omicron.term) Omicron.constant -> a Ast.fundefn Result.t =
  fun env { cnst_ident; cnst_prms; cnst_body; _ } ->
  match cnst_body with
  | None -> failure (fun _ -> "Temporary.constant_to_fundefn")
  | Some term ->
    filter_map_syms env (Array.to_list cnst_prms) >>= fun prms ->
    filter_map_vars env (Array.to_list cnst_prms) >>= fun vars ->
    term_to_term env term >>= fun term ->
    Ok Ast.(mk_fundefn (fst cnst_ident) prms vars term)


and constant_to_fundecl :
  type a. env -> (a Omicron.sort,a Omicron.term) Omicron.constant -> a Ast.fundecl Result.t =
  fun env { cnst_ident; cnst_prms; cnst_type; cnst_body; _ } ->
  match cnst_body with
  | Some _ -> failure (fun  _ -> "Temporary.constant_to_fundecl")
  | None ->
    filter_map_syms env (Array.to_list cnst_prms) >>= fun prms ->
    filter_map_vars env (Array.to_list cnst_prms) >>= fun vars ->
    let vars = List.map (fun v -> v.Ast.var_sort) vars in
    sort_to_sort env cnst_type >>= fun sort ->
    Ok Ast.(mk_fundecl (fst cnst_ident) prms vars sort)


and sort_case_to_cases :
  env -> (set,prop Omicron.kind,prop Omicron.sort) Omicron.case -> prop Ast.case list Result.t =
  fun env { case_indv; case_branches; _ } ->
  Result.Array.map2
    (fun Omicron.{ ctor_name; _ } Omicron.{ bnch_prms; bnch_desc; _ } ->
       filter_map_vars env (Array.to_list bnch_prms) >>= fun vars ->
       sort_to_form env bnch_desc >>= fun form ->
       Ok Ast.(mk_case ctor_name vars form))
    Omicron.((get_one_inductive case_indv).oind_ctors)
    case_branches
  >>= fun array -> Ok (Array.to_list array)


and term_case_to_cases :
  type a. env -> (set,a Omicron.sort,a Omicron.term) Omicron.case -> a Ast.case list Result.t =
  fun env { case_indv; case_branches; _ } ->
  Result.Array.map2
    (fun Omicron.{ ctor_name; _ } Omicron.{ bnch_prms; bnch_desc; _ } ->
       filter_map_vars env (Array.to_list bnch_prms) >>= fun vars ->
       term_to_term env bnch_desc >>= fun term ->
       Ok Ast.(mk_case ctor_name vars term))
    Omicron.((get_one_inductive case_indv).oind_ctors)
    case_branches
  >>= fun array -> Ok (Array.to_list array)


and inductive_to_datatype :
  type a. env -> a Omicron.inductive * int -> Ast.datatype Result.t =
  fun env indv ->
  let oind = Omicron.get_one_inductive indv in
  let name = oind.Omicron.oind_name in
  match find_dttp name env with
  | Some dttp -> Ok dttp
  | None ->
    let env = add_dttp (Ast.mk_datatype name [] []) env in
    filter_map_syms env (Omicron.get_arrows oind.Omicron.oind_kind |> snd ) >>= fun dttp_prms ->
    Result.Array.map (constructor_to_constructor env dttp_prms) oind.oind_ctors
    >>= fun constructors ->
    let dttp = Ast.mk_datatype name dttp_prms (Array.to_list constructors) in
    replace_dttp dttp env;
    Log.Verbose.debug
      ~head:(fun fmt -> fmt "inductive_to_datatype")
      ~body:(fun fmt -> fmt "%a" Ast_pp.pp_datatype dttp);
    Ok dttp


and constructor_to_constructor :
  type a. env -> string list -> a Omicron.constructor -> Ast.constructor Result.t =
  fun env dttp_prms Omicron.{ ctor_name; ctor_sort; _ } ->
  let products = Omicron.get_products ctor_sort |> snd in
  filter_map_syms env products >>= fun ctor_prms ->
  List.iter2 (fun dp cp -> add_name cp dp env) dttp_prms ctor_prms;
  filter_map_vars ~f:name_anonymous env products >>= fun list ->
  let selectors =
    List.mapi
      Ast.(fun n { var_name; var_sort; _ } ->
          mk_selector
            (if String.contains var_name '<' then Printf.sprintf "@%i%s" n ctor_name else var_name)
            var_sort)
      list
  in
  Ok (Ast.mk_constructor ctor_name selectors)


and inductive_to_relation :
  env -> prop Omicron.inductive * int (*-> Omicron.sort_or_term array*) -> Ast.relation Result.t =
  fun env indv (*array*) ->
  let oind = Omicron.get_one_inductive indv in
  let name = rela_name oind.Omicron.oind_name in
  match find_rela name env with
  | Some rela -> Ok rela
  | None ->
    let env = add_rela (Ast.mk_relation name []) env in
    Result.List.filter_map
      (function
        | Omicron.Sym _ -> Ok None
        | Omicron.Var v ->
          match Omicron.witness v.Omicron.var_kind with
          | Prop -> failure (fun _ -> "Temporary.inductive_to_relation")
          | Set  ->
            sort_to_sort env v.Omicron.var_sort >>= fun (sort: set Ast.sort) ->
            Ok (Some sort))
      (Omicron.get_arrows oind.Omicron.oind_kind |> snd)
    >>= fun prms ->
    (*filter_map_set_sort_list_result env (Array.to_list array) >>= fun list ->*)
    let rela = Ast.mk_relation name prms in
    (*push (Ast.Relation rela);*)
    replace_rela rela env;
    inductive_to_rules env rela indv >>= fun list ->
    List.iter (fun rule -> push (Ast.Rule rule)) list;
    Ok rela


and constructor_to_rule :
  env -> Ast.relation -> prop Omicron.constructor -> Ast.rule Result.t =
  fun env rela { ctor_name; ctor_sort; _ } ->
  let sort, list = Omicron.get_products ctor_sort in
  match sort.Omicron.sort_desc with
  | StInductive (_, array) ->
    filter_map_set_terms env (Array.to_list array) >>= fun terms ->
    filter_map_vars env list >>= fun vars ->
    Result.List.fold_right
      (fun sym_or_var right ->
         match sym_or_var with
         | Omicron.Sym _ -> Ok right
         | Omicron.Var v ->
           match v.Omicron.var_name with
           | Id _ | Name _ -> Ok right
           | Anonymous ->
             match Omicron.witness v.Omicron.var_kind with
             | Set  -> failure (fun _ -> "Temporary.constructor_to_rule")
             | Prop ->
               sort_to_form env v.Omicron.var_sort >>= fun (left: prop Ast.term) ->
               Ok (Ast.mk_term_imply left right))
      list
      (Ok Ast.(mk_term_decl (relation_to_fundecl rela) [] (terms)))
    >>= fun desc ->
    Ok (Ast.mk_rule ctor_name rela.Ast.rela_name vars desc)
  | _ -> failure (fun _ -> "Temporary.construtor_to_rule")


and inductive_to_rules :
  env -> Ast.relation -> prop Omicron.inductive * int -> Ast.rule list Result.t =
  fun env rela indv ->
  Result.List.map
    (constructor_to_rule env rela)
    (Array.to_list Omicron.((get_one_inductive indv).oind_ctors))


and filter_map_vars ?(f=Fun.id) env list =
  Result.List.filter_map
    (function
      | Omicron.Sym _ -> Ok None
      | Omicron.Var v ->
        match Omicron.witness v.Omicron.var_kind, f v.Omicron.var_name with
        | Set, (Id _ | Name _) -> var_to_var env v >>= fun v -> Ok (Some v)
        | _ -> Ok None)
    list

and filter_map_syms ?(f=Fun.id) env list =
  Result.List.filter_map
    (function
      | Omicron.Var _ -> Ok None
      | Omicron.Sym s ->
        match Omicron.witness s.Omicron.sym_kind, f s.Omicron.sym_name with
        | Set, (Id _ | Name _) -> sym_to_sym env s >>= fun s -> Ok (Some s)
        | _ -> Ok None)
    list

and filter_map_set_sorts env list =
  Result.List.filter_map
    (function
      | Omicron.Term _ -> Ok None
      | Omicron.Sort st ->
        match Omicron.witness st.Omicron.sort_kind with
        | Prop -> Ok None
        | Set  ->
          sort_to_sort env st >>= fun (st: set Ast.sort) ->
          Ok (Some st))
    list


and filter_map_set_terms env list =
  Result.List.filter_map
    (function
      | Omicron.Sort _ -> Ok None
      | Omicron.Term tm ->
        match Omicron.witness tm.Omicron.term_kind with
        | Prop -> Ok None
        | Set  ->
          term_to_term env tm >>= fun (tm: set Ast.term) ->
          Ok (Some tm))
    list


and ensure_prop_sort : env -> Omicron.sort_or_term -> prop Ast.term Result.t =
  fun env sort_or_term ->
  match sort_or_term with
  | Omicron.Term _ -> failure (fun _ -> "Temporary.ensure_prop_sort")
  | Omicron.Sort st ->
    match Omicron.witness st.Omicron.sort_kind with
    | Prop -> sort_to_form env st
    | Set  -> failure (fun _ -> "Temporary.ensure_prop_sort")


and ensure_set_sort : env -> Omicron.sort_or_term -> set Ast.sort Result.t =
  fun env sort_or_term ->
  match sort_or_term with
  | Omicron.Term _ -> failure (fun _ -> "Temporary.ensure_set_sort")
  | Omicron.Sort st ->
    match Omicron.witness st.Omicron.sort_kind with
    | Prop -> failure (fun _ -> "Temporary.ensure_set_sort")
    | Set  -> sort_to_sort env st


and ensure_prop_term : env -> Omicron.sort_or_term -> prop Ast.term Result.t =
  fun env sort_or_term ->
  match sort_or_term with
  | Omicron.Sort _ -> failure (fun _ -> "Temporary.ensure_prop_term")
  | Omicron.Term tm ->
    match Omicron.witness tm.Omicron.term_kind with
    | Prop -> term_to_term env tm
    | Set  -> failure (fun _ -> "Temporary.ensure_prop_term")


and ensure_set_term : env -> Omicron.sort_or_term -> set Ast.term Result.t =
  fun env sort_or_term ->
  match sort_or_term with
  | Omicron.Sort _ ->  failure (fun _ -> "Temporary.ensure_set_term")
  | Omicron.Term tm ->
    match Omicron.witness tm.Omicron.term_kind with
    | Prop -> failure (fun _ -> "Temporary.ensure_set_term")
    | Set  -> term_to_term env tm

(*
let term_to_rule : prop Omicron.term -> Ast.rule Result.t =
  fun term ->
  match term.Omicron.term_desc with
  | TmConstant (cn,_) ->
    Result.Array.fold_right
      (fun sym_or_var list ->
         match sym_or_var with
         | Omicron.Sym _ -> failure (fun _ -> "Temporary.omicron_to_relation")
         | Omicron.Var v ->
           var_to_var empty v >>= fun v ->
           Ok (v :: list))
      cn.cnst_prms (Ok []) >>= fun list ->
    sort_to_term empty cn.cnst_type >>= fun term ->
    Ok (Ast.mk_rule (ident_to_string cn.Omicron.cnst_name) list term)
  | _ -> failure (fun _ -> "Temporary.omicron_to_rule : not a constant")


let term_to_relation : prop Omicron.term -> Ast.relation Result.t =
  fun term ->
  match term.Omicron.term_desc with
  | TmConstant (cn,_) ->
    Result.Array.fold_right
      (fun sym_or_var list ->
         match sym_or_var with
         | Omicron.Sym _ -> failure (fun _ -> "Temporary.omicron_to_relation")
         | Omicron.Var v ->
           sort_to_sort empty v.Omicron.var_sort >>= fun sort ->
           Ok (sort :: list))
      cn.cnst_prms (Ok []) >>= fun list ->
    Ok (Ast.mk_relation (ident_to_string cn.Omicron.cnst_name) list)
  | _ -> failure (fun _ -> "Temporary.omicron_to_relation : not a constant")
*)


let constant_to_rule :
  env -> (prop Omicron.sort,prop Omicron.term) Omicron.constant -> Ast.rule Result.t =
  fun env { cnst_ident; cnst_type; _ } ->
  let sort, list = Omicron.get_products cnst_type in
  match sort.Omicron.sort_desc with
  | StInductive (indv, array) ->
    inductive_to_relation env indv >>= fun rela ->
    filter_map_set_terms env (Array.to_list array) >>= fun terms ->
    filter_map_vars env list >>= fun vars ->
    Result.List.fold_right
      (fun sym_or_var right ->
         match sym_or_var with
         | Omicron.Sym _ -> Ok right
         | Omicron.Var v ->
           match v.Omicron.var_name with
           | Id _ | Name _ -> Ok right
           | Anonymous ->
             match Omicron.witness v.Omicron.var_kind with
             | Set  -> failure (fun _ -> "Temporary.constant_to_rule")
             | Prop ->
               sort_to_form env v.Omicron.var_sort >>= fun (left: prop Ast.term) ->
               Ok (Ast.mk_term_imply left right))
      list
      (Ok Ast.(mk_term_decl (relation_to_fundecl rela) [] (terms)))
    >>= fun desc ->
    Ok (Ast.mk_rule (fst cnst_ident) rela.Ast.rela_name vars desc)
  | _ -> failure (fun _ -> "Temporary.constant_to_rule")


let extract_inductive :
  (prop Omicron.inductive * int) -> lemmas:(prop Omicron.sort,prop Omicron.term) Omicron.constant list ->
  Ast.t list Result.t =
  fun indv ~lemmas ->
  let env = create 17 in
  inductive_to_relation env indv >>= fun rela ->
  Result.List.map (constant_to_rule env) lemmas >>= fun lemmas ->
  List.iter (fun rule -> push (Ast.Rule rule)) lemmas;
  push (Ast.Query rela);
  Ok (flush ())

