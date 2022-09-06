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

open Smtlib

let horn = ref false

let fold_map_list f list env =
  List.fold_right
    (fun t (list, env) ->
       let t, env = f t env in
       t :: list, env)
    list ([], env)

let create_register_lookup to_string =
  let table = Utils.StringHashtbl.create 17 in
  (fun value -> Utils.StringHashtbl.add table (to_string value) value),
  (fun string -> Utils.StringHashtbl.find_opt table string)

let register_sdef, lookup_sdef = create_register_lookup (fun sdef -> sdef.Ast.sdef_name)
let register_dttp, lookup_dttp = create_register_lookup (fun dttp -> dttp.Ast.dttp_name)
let register_sfdc, lookup_sfdc = create_register_lookup (fun fdec -> fdec.Ast.fdec_name)
let register_pfdc, lookup_pfdc = create_register_lookup (fun fdec -> fdec.Ast.fdec_name)
let register_sfdf, lookup_sfdf = create_register_lookup (fun fdef -> fdef.Ast.fdef_name)
let register_pfdf, lookup_pfdf = create_register_lookup (fun fdef -> fdef.Ast.fdef_name)

let () = register_dttp
    Ast.(mk_datatype "bool" []
           [mk_constructor "true" [];
            mk_constructor "false" []])


let get_identifier_name id =
  match id.id_desc with
  | IdSymbol s
  | IdUnderscore (s, _) -> s.symbol_desc

let get_qual_identifier_name qid =
  match qid.qual_identifier_desc with
  | QualIdentifierIdentifier id
  | QualIdentifierAs (id, _) -> get_identifier_name id

let mk_identifier_name name = mk_id_symbol (mk_symbol name)

let mk_sort_name name = mk_sort_identifier (mk_identifier_name name)
let mk_sort_fun_name name list = mk_sort_fun (mk_identifier_name name) list

let mk_term_name name =
  mk_term_qual_identifier
    (mk_qual_identifier_identifier
       (mk_identifier_name name))

let mk_term_name_terms name terms =
  mk_term_qual_identifier_terms
    (mk_qual_identifier_identifier
       (mk_identifier_name name))
    terms


let rec sort_to_sort : type a. a Ast.sort -> 'env -> sort * 'env  =
  fun sort env ->
  match sort.Ast.sort_desc with
  | Ast.SortProp -> mk_sort_name "Bool", env
  | Ast.SortBool -> mk_sort_name "Bool", env
  | Ast.SortInt -> mk_sort_name "Int", env
  | Ast.SortSymbol string -> mk_sort_name string, env
  | Ast.SortArray s ->
    let s, env = sort_to_sort s env in
    mk_sort_fun_name "Array" [mk_sort_name "Int"; s], env
  | Ast.SortDatatype (dttp, list) ->
    let dttp, env = on_dttp dttp list env in
    mk_sort_name dttp.Ast.dttp_name, env
  | Ast.SortDefn (sdef, list) ->
    let sdef, env = on_sdef sdef list env in
    mk_sort_name sdef.Ast.sdef_name, env

and sortdef_to_command sdef env =
  let desc, env = sort_to_sort sdef.Ast.sdef_desc env in
  mk_cmd_define_sort
    (mk_symbol sdef.Ast.sdef_name)
    (List.map mk_symbol sdef.Ast.sdef_prms)
    desc,
  env

and selector_to_selector slct env =
  let sort, env = sort_to_sort slct.Ast.slct_sort env in
  mk_selector_dec (mk_symbol slct.Ast.slct_name) sort, env

and constructor_to_constructor cnsr env =
  let selectors, env = fold_map_list selector_to_selector cnsr.Ast.selectors env in
  mk_constructor_dec (mk_symbol cnsr.Ast.cnsr_name) selectors, env

and datatype_to_command dttp env =
  let constructors, env = fold_map_list constructor_to_constructor dttp.Ast.constructors env in
  mk_cmd_declare_datatype
    (mk_symbol dttp.Ast.dttp_name)
    (mk_datatype_dec (List.map mk_symbol dttp.Ast.dttp_prms) constructors),
  env

and on_sdef sdef list env =
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = sdef.Ast.sdef_name ^ concat in
  match lookup_sdef name with
  | Some sdef -> sdef, env
  | None ->
    let sdef =
      Ast.mk_sortdefn name []
        (Ast_utils.subst_sort_list
           (List.combine sdef.Ast.sdef_prms list)
           sdef.Ast.sdef_desc)
    in
    register_sdef sdef;
    sdef,
    let sdef, env = sortdef_to_command sdef env in
    sdef :: env

and on_dttp dttp list env =
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = dttp.Ast.dttp_name ^ concat in
  match lookup_dttp name with
  | Some dttp -> dttp, env
  | None ->
    let list = List.combine dttp.Ast.dttp_prms list in
    let dttp =
      Ast.mk_datatype name []
        (List.map (fun cnsr ->
             Ast.mk_constructor (cnsr.Ast.cnsr_name ^ concat)
               (List.map (fun slct ->
                    Ast.mk_selector (slct.Ast.slct_name ^ concat)
                      (Ast_utils.subst_sort_list list slct.Ast.slct_sort))
                   cnsr.Ast.selectors))
            dttp.constructors)
    in
    register_dttp dttp;
    dttp,
    let dttp, env = datatype_to_command dttp env in
    dttp :: env


let var_to_symbol var =
  (mk_symbol var.Ast.var_name)

let var_to_sorted_var var env =
  let sort, env = sort_to_sort var.Ast.var_sort env in
  mk_sorted_var (mk_symbol var.Ast.var_name) sort, env

let flatten_term_qual_identifier_terms string terms =
  List.flatten
    (List.map
       (fun t ->
          match t.term_desc with
          | TermQualIdentifierTerms (qid, list) ->
            if String.equal string (get_qual_identifier_name qid)
            then list else [t]
          | _ -> [t])
       terms)


let rec term_to_term : type a. a Ast.term -> 'env -> term * 'env =
  fun term env ->
  match term.Ast.term_desc with
  | Ast.TermTrue  -> mk_term_spec_constant (Smtlib.CstBool true), env
  | Ast.TermFalse -> mk_term_spec_constant (Smtlib.CstBool false), env
  | Ast.TermBool bool -> mk_term_spec_constant (Smtlib.CstBool bool), env
  | Ast.TermInt int -> mk_term_spec_constant (CstNumeral int), env

  | Ast.TermVar v ->
    let _, env = var_to_sorted_var v env in
    mk_term_name v.Ast.var_name, env

  | Ast.TermLet (v, b, t) ->
    let b, env = term_to_term b env in
    let t, env = term_to_term t env in
    (match t.term_desc with
     | TermLetTerm (list, t) ->
       mk_term_let_term (mk_var_binding (var_to_symbol v) b :: list) t, env
     | _ ->
       mk_term_let_term [mk_var_binding (var_to_symbol v) b] t, env)

  | Ast.TermExists (v, f) ->
    let v, env = var_to_sorted_var v env in
    let f, env = term_to_term f env in
    (match f.term_desc with
     | TermExistsTerm (list, t) ->
       mk_term_exists_term (v :: list) t, env
     | _ ->
       mk_term_exists_term [v] f, env)

  | Ast.TermForall (v, f) ->
    let v, env = var_to_sorted_var v env in
    let f, env = term_to_term f env in
    (match f.term_desc with
     | TermForallTerm (list, t) ->
       mk_term_forall_term (v :: list) t, env
     | _ ->
       mk_term_forall_term [v] f, env)

  | Ast.TermMatch (t, list) ->
    let concat =
      match t.Ast.term_sort.Ast.sort_desc with
      | Ast.SortDatatype (_, list) ->
        String.concat "" (List.map Ast_utils.sort_to_string list)
      | _ -> ""
    in
    let t, env = term_to_term t env in
    let list, env = fold_map_list (term_case_to_case concat) list env in
    mk_term_match_term t list, env

  | Ast.TermIte (f, t1, t2) ->
    let f,  env = term_to_term f  env in
    let t1, env = term_to_term t1 env in
    let t2, env = term_to_term t2 env in
    mk_term_name_terms "ite" [f; t1; t2], env

  | Ast.TermVariadic (v, list) ->
    let list, env = fold_map_list term_to_term list env in
    (match v with
     | Ast.Distinct -> mk_term_name_terms "distinct" list, env)

  | Ast.TermUnop (u, t) ->
    (match u with
     | Ast.Classic -> term_to_term t env
     | Ast.Not ->
       let t, env = term_to_term t env in
       mk_term_name_terms "not" [t], env
     | Ast.Succ -> fold_succ 1 t env)

  | Ast.TermBnop (b, t1, t2) ->
    let t1, env = term_to_term t1 env in
    let t2, env = term_to_term t2 env in
    (match b with
     | Ast.Imply -> mk_term_name_terms "=>" [t1; t2]
     | Ast.And -> mk_term_name_terms "and" (flatten_term_qual_identifier_terms "and" [t1; t2])
     | Ast.Or -> mk_term_name_terms "or" (flatten_term_qual_identifier_terms "or" [t1; t2])
     | Ast.Equal -> mk_term_name_terms "=" [t1; t2]
     | Ast.Le -> mk_term_name_terms "<=" [t1; t2]
     | Ast.Lt -> mk_term_name_terms "<" [t1; t2]
     | Ast.Ge -> mk_term_name_terms ">=" [t1; t2]
     | Ast.Gt -> mk_term_name_terms ">" [t1; t2]
     | Ast.Add -> mk_term_name_terms "+" [t1; t2]
     | Ast.Sub -> mk_term_name_terms "-" [t1; t2]),
    env

  | Ast.TermDefn (fdef, sorts, list) ->
    let (fdef: a Ast.fundefn), env =
      match Ast.kind fdef.Ast.fdef_desc.Ast.term_sort with
      | Ast.KindProp -> on_prop_fdef fdef sorts env
      | Ast.KindSet -> on_set_fdef fdef sorts env
    in
    let list, env = fold_map_list term_to_term list env in
    (match list with
     | [] -> mk_term_name fdef.Ast.fdef_name, env
     | list -> mk_term_name_terms fdef.Ast.fdef_name list, env)

  | Ast.TermDecl (fdec, sorts, list) ->
    let (fdec: a Ast.fundecl), env =
      match Ast.kind fdec.Ast.fdec_desc with
      | Ast.KindProp -> on_prop_fdec fdec sorts env
      | Ast.KindSet -> on_set_fdec fdec sorts env
    in
    let list, env = fold_map_list term_to_term list env in
    (match list with
     | [] -> mk_term_name fdec.Ast.fdec_name, env
     | list -> mk_term_name_terms fdec.Ast.fdec_name list, env)

  | Ast.TermConstruct (dttp, sorts, int, list) ->
    let dttp, env = on_dttp dttp sorts env in
    let name = (List.nth dttp.Ast.constructors int).Ast.cnsr_name in
    let list, env = fold_map_list term_to_term list env in
    (match list with
     | [] -> mk_term_name name, env
     | list -> mk_term_name_terms name list, env)

  | Ast.TermSelect (dttp, sorts, int1, int2, t) ->
    let dttp, env = on_dttp dttp sorts env in
    let t, env = term_to_term t env in
    mk_term_name_terms
      (List.nth
         (List.nth dttp.Ast.constructors int1).Ast.selectors
         int2).Ast.slct_name
      [t], env

  | Ast.ArrayConst (s, t) ->
    let s, env = sort_to_sort (Ast.mk_sort_array s) env in
    let t, env = term_to_term t env in
    mk_term_qual_identifier_terms
      (mk_qual_identifier_as  (mk_identifier_name "const") s)
      [t], env

  | Ast.ArrayRead (_, a, i) ->
    let a, env = term_to_term a env in
    let i, env = term_to_term i env in
    mk_term_name_terms "select" [a; i], env

  | Ast.ArrayWrite (_, a, i, e) ->
    let a, env = term_to_term a env in
    let i, env = term_to_term i env in
    let e, env = term_to_term e env in
    mk_term_name_terms "store" [a; i; e], env

  | Ast.ArrayMap _ -> assert false

  | Ast.ArrayDistinct _ -> assert false

and fold_succ : type a. int -> a Ast.term -> 'env -> term * 'env =
  fun i t env ->
  match t.Ast.term_desc with
  | Ast.TermInt int -> mk_term_spec_constant (CstNumeral (int + i)), env
  | Ast.TermUnop (Ast.Succ, t) -> fold_succ (i + 1) t env
  | _ ->
    let t, env = term_to_term t env in
    mk_term_name_terms "+" [t; mk_term_spec_constant (CstNumeral i)], env

and fundecl_to_command : type a. a Ast.fundecl -> 'env -> command * 'env =
  fun fdec env ->
  let vars, env = fold_map_list sort_to_sort fdec.Ast.fdec_vars env in
  let desc, env = sort_to_sort fdec.Ast.fdec_desc env in
  match Ast.kind fdec.Ast.fdec_desc with
  | Ast.KindProp ->
    (if !horn then
       mk_cmd_declare_rel
         (mk_symbol fdec.Ast.fdec_name)
         vars
     else
       mk_cmd_declare_fun
         (mk_symbol fdec.Ast.fdec_name)
         vars
         (mk_sort_name "Bool")),
    env
  | Ast.KindSet ->
    mk_cmd_declare_fun
      (mk_symbol fdec.Ast.fdec_name)
      vars desc,
    env

and fundefn_to_command : type a. a Ast.fundefn -> 'env -> command * 'env =
  fun fdef env ->
  let vars, env = fold_map_list var_to_sorted_var fdef.Ast.fdef_vars env in
  let sort, env = sort_to_sort fdef.Ast.fdef_desc.Ast.term_sort env in
  let desc, env = term_to_term fdef.Ast.fdef_desc env in
  mk_cmd_define_fun
    (mk_symbol fdef.Ast.fdef_name)
    vars sort desc,
  env

and term_case_to_case : type a. string -> a Ast.case -> 'env -> match_case * 'env =
  fun concat case env ->
  let t, env = term_to_term case.Ast.case_desc env in
  let p =
    mk_pattern
      (mk_symbol (case.Ast.case_name ^ concat))
      (List.map var_to_symbol case.Ast.case_vars)
  in
  mk_match_case p t, env

and on_prop_fdec : Ast.prop Ast.fundecl -> Ast.set Ast.sort list -> 'env -> Ast.prop Ast.fundecl * 'env =
  fun fdec list env ->
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = fdec.Ast.fdec_name ^ concat in
  match lookup_pfdc name with
  | Some fdec -> fdec, env
  | None ->
    let list = List.combine fdec.Ast.fdec_prms list in
    let fdec =
      Ast.mk_fundecl name []
        (List.map (Ast_utils.subst_sort_list list) fdec.Ast.fdec_vars)
        (Ast_utils.subst_sort_list list fdec.Ast.fdec_desc)
    in
    register_pfdc fdec;
    fdec,
    let fdec, env = fundecl_to_command fdec env in
    fdec :: env

and on_set_fdec : Ast.set Ast.fundecl -> Ast.set Ast.sort list -> 'env -> Ast.set Ast.fundecl * 'env =
  fun fdec list env ->
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = fdec.Ast.fdec_name ^ concat in
  match lookup_sfdc name with
  | Some fdec -> fdec, env
  | None ->
    let list = List.combine fdec.Ast.fdec_prms list in
    let fdec =
      Ast.mk_fundecl name []
        (List.map (Ast_utils.subst_sort_list list) fdec.Ast.fdec_vars)
        (Ast_utils.subst_sort_list list fdec.Ast.fdec_desc)
    in
    register_sfdc fdec;
    fdec,
    let fdec, env = fundecl_to_command fdec env in
    fdec :: env

and on_prop_fdef : Ast.prop Ast.fundefn -> Ast.set Ast.sort list -> 'env -> Ast.prop Ast.fundefn * 'env =
  fun fdef list env ->
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = fdef.Ast.fdef_name ^ concat in
  match lookup_pfdf name with
  | Some fdef -> fdef, env
  | None ->
    let list = List.combine fdef.Ast.fdef_prms list in
    let fdef =
      Ast.mk_fundefn name []
        (List.map (fun v ->
             Ast.mk_variable v.Ast.var_name (Ast_utils.subst_sort_list list v.Ast.var_sort))
            fdef.Ast.fdef_vars)
        (Ast_utils.subst_term_list list [] fdef.Ast.fdef_desc)
    in
    register_pfdf fdef;
    fdef,
    let fdef, env = fundefn_to_command fdef env in
    fdef :: env

and on_set_fdef : Ast.set Ast.fundefn -> Ast.set Ast.sort list -> 'env -> Ast.set Ast.fundefn * 'env =
  fun fdef list env ->
  let concat = String.concat "" (List.map Ast_utils.sort_to_string list) in
  let name = fdef.Ast.fdef_name ^ concat in
  match lookup_sfdf name with
  | Some fdef -> fdef, env
  | None ->
    let list = List.combine fdef.Ast.fdef_prms list in
    let fdef =
      Ast.mk_fundefn name []
        (List.map (fun v ->
             Ast.mk_variable v.Ast.var_name (Ast_utils.subst_sort_list list v.Ast.var_sort))
            fdef.Ast.fdef_vars)
        (Ast_utils.subst_term_list list [] fdef.Ast.fdef_desc)
    in
    register_sfdf fdef;
    fdef,
    let fdef, env = fundefn_to_command fdef env in
    fdef :: env


let declare_var =
  let table = Utils.StringHashtbl.create 17 in
  (fun env v ->
     match Utils.StringHashtbl.find_opt table v.Ast.var_name with
     | Some Ast.{ var_sort; _ } ->
       if Ast.equal var_sort v.Ast.var_sort then env
       else
         failwith
           (Printf.sprintf
              "Multiple definitions of '%s' with incompatible sorts"
              v.Ast.var_name)
     | None ->
       Utils.StringHashtbl.add table v.Ast.var_name v;
       let sort, env = sort_to_sort v.Ast.var_sort env in
       mk_cmd_declare_var
         (mk_symbol v.Ast.var_name)
         sort :: env)

let finalize t list = List.rev (t :: list)

let ast_to_horn t env =
  match t with
  | Ast.Datatype dttp ->
    (match dttp.Ast.dttp_prms with
     | [] ->
       register_dttp dttp;
       let dttp, env = datatype_to_command dttp env in
       finalize dttp env
     | _ -> [])

  | Ast.Function fdef ->
    (match fdef.Ast.fdef_prms with
     | [] ->
       register_sfdf fdef;
       let fdef, env = fundefn_to_command fdef env in
       finalize fdef env
     | _ -> [])

  | Ast.Predicate fdef ->
    (match fdef.Ast.fdef_prms with
     | [] ->
       register_pfdf fdef;
       let fdef, env = fundefn_to_command fdef env in
       finalize fdef env
     | _ -> [])

  | Ast.Query rela ->
    finalize
      (mk_cmd_query (mk_symbol rela.Ast.rela_name))
      env

  | Ast.Relation rela ->
    let prms, env = fold_map_list sort_to_sort rela.Ast.rela_prms env in
    finalize
      (mk_cmd_declare_rel
         (mk_symbol rela.Ast.rela_name)
         prms)
      env

  | Ast.Rule rule ->
    (match rule.Ast.rule_desc.Ast.term_desc with
     | Ast.TermTrue -> []
     | Ast.TermFalse -> assert false
     | _ ->
       let env = List.fold_left declare_var env rule.Ast.rule_vars in
       let env = List.fold_left declare_var env rule.Ast.rule_desc.Ast.term_free in
       let desc, env = term_to_term rule.Ast.rule_desc env in
       (finalize (mk_cmd_rule desc (Some (mk_symbol rule.Ast.rule_name))) env))

  | Ast.Sort sdef ->
    register_sdef sdef;
    (match sdef.Ast.sdef_prms with
     | [] ->
       register_sdef sdef;
       let sdef, env = sortdef_to_command sdef env in
       finalize sdef env
     | _ -> [])


let ast_to_smtlib t env =
  match t with
  | Ast.Datatype dttp ->
    (match dttp.Ast.dttp_prms with
     | [] ->
       register_dttp dttp;
       let dttp, env = datatype_to_command dttp env in
       finalize dttp env
     | _ -> [])

  | Ast.Function fdef ->
    (match fdef.Ast.fdef_prms with
     | [] ->
       register_sfdf fdef;
       let fdef, env = fundefn_to_command fdef env in
       finalize fdef env
     | _ -> [])

  | Ast.Predicate fdef ->
    (match fdef.Ast.fdef_prms with
     | [] ->
       register_pfdf fdef;
       let fdef, env = fundefn_to_command fdef env in
       finalize fdef env
     | _ -> [])

  | Ast.Query rela ->
     let var_names = List.map (fun s ->
                         Printf.sprintf "%s%s" (Ast_utils.sort_to_string s)
                           (Utils.Name.to_string (Utils.Name.fresh ())))
                       rela.Ast.rela_prms in
     let vars = List.map2 Ast.mk_variable var_names rela.Ast.rela_prms in
     let sorted_vars, env = fold_map_list var_to_sorted_var vars env in
     let desc, env = term_to_term Ast.(mk_term_imply
                                         (mk_term_decl (Temporary.relation_to_fundecl rela) []
                                            (List.map Ast.mk_term_var vars))
                                         mk_term_false) env in
     let rule = mk_cmd_assert (mk_term_forall_term sorted_vars desc) in
     finalize mk_cmd_check_sat (finalize rule env)

  | Ast.Relation rela ->
    let prms, env = fold_map_list sort_to_sort rela.Ast.rela_prms env in
    finalize
      (mk_cmd_declare_fun
         (mk_symbol rela.Ast.rela_name)
         prms
         (mk_sort_name "Bool"))
      env

  | Ast.Rule rule ->
    (match rule.Ast.rule_desc.Ast.term_desc with
     | Ast.TermTrue -> []
     | Ast.TermFalse -> assert false
     | _ ->
       let vars, env =
         fold_map_list
           var_to_sorted_var
           (List.sort_uniq compare (rule.Ast.rule_vars @ rule.Ast.rule_desc.Ast.term_free))
           env
       in
       let desc, env = term_to_term rule.Ast.rule_desc env in
       (finalize (mk_cmd_assert (mk_term_forall_term vars desc)) env))

  | Ast.Sort sdef ->
    register_sdef sdef;
    (match sdef.Ast.sdef_prms with
     | [] ->
       register_sdef sdef;
       let sdef, env = sortdef_to_command sdef env in
       finalize sdef env
     | _ -> [])


let term_to_term t = term_to_term t [] |> fst

let ast_to_horn t = horn := true; ast_to_horn t []
let ast_to_smtlib t = horn := false; ast_to_smtlib t []

