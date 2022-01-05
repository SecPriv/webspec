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

module VarMap = Map.Make
    (struct
      type t = Ast.var
      let compare t1 t2 = compare t1 t2
    end)

let get_constructor d i = List.nth d.Ast.constructors i
let get_selector d i1 i2 = List.nth (get_constructor d i1).Ast.selectors i2

let get_name (t: Ast.t) =
  match t with
  | Ast.Sort sdef -> sdef.Ast.sdef_name
  | Ast.Datatype dttp -> dttp.Ast.dttp_name
  | Ast.Function fdef -> fdef.Ast.fdef_name
  | Ast.Predicate pdef -> pdef.Ast.fdef_name
  | Ast.Relation rela -> rela.Ast.rela_name
  | Ast.Query rela -> rela.Ast.rela_name
  | Ast.Rule rule -> rule.Ast.rule_name

let rec sort_to_string : type a. a Ast.sort -> string  =
  fun sort ->
  match sort.Ast.sort_desc with
  | Ast.SortProp -> "Bool"
  | Ast.SortBool -> "Bool"
  | Ast.SortInt -> "Int"
  | Ast.SortSymbol string -> string
  | Ast.SortArray sort ->
    Printf.sprintf "Array%s" (sort_to_string sort)
  | Ast.SortDatatype (dttp, list) ->
    Printf.sprintf "%s%s"
      dttp.Ast.dttp_name
      (String.concat "" (List.map sort_to_string list))
  | Ast.SortDefn (sdef, list) ->
    Printf.sprintf "%s%s"
      sdef.Ast.sdef_name
      (String.concat "" (List.map sort_to_string list))

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

let bind_identity = {
  bind_sort = (fun ~before:_ ~after env -> after, env);
  bind_defn = (fun ~before:_ ~after env -> after, env);
  bind_decl = (fun ~before:_ ~after env -> after, env);
  unbind_sort = (fun ~before:_ ~after env -> after, env);
  unbind_defn = (fun ~before:_ ~after env -> after, env);
  unbind_decl = (fun ~before:_ ~after env -> after, env);
}

type 'a fold_map = {
  fold_map_sort : 'b. ('b Ast.sort, 'a) fn;
  fold_map_term : 'b. ('b Ast.term, 'a) fn;
  fold_map_dttp : (Ast.datatype, 'a) fn;
  fold_map_sdef : (Ast.sortdefn,  'a) fn;
  fold_map_fdec : 'b. ('b Ast.fundecl, 'a) fn;
  fold_map_fdef : 'b. ('b Ast.fundefn, 'a) fn;
  fold_map_var  : (Ast.var, 'a) fn;
}

let fold_map_identity = {
  fold_map_sort = (fun ~before:_ ~after env -> after, env);
  fold_map_term = (fun ~before:_ ~after env -> after, env);
  fold_map_dttp = (fun ~before:_ ~after env -> after, env);
  fold_map_sdef = (fun ~before:_ ~after env -> after, env);
  fold_map_fdef = (fun ~before:_ ~after env -> after, env);
  fold_map_fdec = (fun ~before:_ ~after env -> after, env);
  fold_map_var  = (fun ~before:_ ~after env -> after, env);
}

let fold_map_list f list env =
  List.fold_right
    (fun t (list, env) ->
       let t, env = f t env in
       t :: list, env)
    list ([], env)

let fold_map_list2 f ~before ~after env =
  List.fold_right2
    (fun before after (list, env) ->
       let t, env = f ~before ~after env in
       t :: list, env)
    before after ([], env)

let rec fold_map_sort : type a b. a bind -> a fold_map -> b Ast.sort -> a -> b Ast.sort * a =
  fun bd fm before env ->
  match before.Ast.sort_desc with
  | Ast.SortProp -> fm.fold_map_sort ~before ~after:before env
  | Ast.SortBool -> fm.fold_map_sort ~before ~after:before env
  | Ast.SortInt  -> fm.fold_map_sort ~before ~after:before env
  | Ast.SortSymbol _ -> fm.fold_map_sort ~before ~after:before env

  | Ast.SortArray sort ->
    let sort', env = fold_map_sort bd fm sort env in
    fm.fold_map_sort ~before ~after:Ast.(mk_sort_array sort') env
  | Ast.SortDatatype (dttp, list) ->
    let dttp', env = fold_map_dttp bd fm dttp env in
    let list', env = fold_map_list (fold_map_sort bd fm) list env in
    fm.fold_map_sort ~before ~after:Ast.(mk_sort_datatype dttp' list') env
  | Ast.SortDefn (sdef, list) ->
    let sdef', env = fold_map_sdef bd fm sdef env in
    let list', env = fold_map_list (fold_map_sort bd fm) list env in
    fm.fold_map_sort ~before ~after:Ast.(mk_sort_defn sdef' list') env

and fold_map_term : type a b. a bind -> a fold_map -> b Ast.term -> a -> b Ast.term * a =
  fun bd fm before env ->
  match before.Ast.term_desc with
  | Ast.TermTrue   -> fm.fold_map_term ~before ~after:before env
  | Ast.TermFalse  -> fm.fold_map_term ~before ~after:before env
  | Ast.TermBool _ -> fm.fold_map_term ~before ~after:before env
  | Ast.TermInt  _ -> fm.fold_map_term ~before ~after:before env

  | Ast.TermVar var ->
    let var', env = fold_map_var bd fm var env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_var var') env
  | Ast.TermLet (var, bind, term) ->
    let var',  env = fold_map_var bd fm var env in
    let bind', env = fold_map_term bd fm bind env in
    let (var',bind'), env = bd.bind_defn ~before:(var,bind) ~after:(var',bind') env in
    let term', env = fold_map_term bd fm term env in
    let (var',bind'), env = bd.unbind_defn ~before:(var,bind) ~after:(var',bind') env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_let var' bind' term') env
  | Ast.TermExists (var, form) ->
    let var',  env = fold_map_var bd fm var env in
    let var',  env = bd.bind_decl ~before:var ~after:var' env in
    let form', env = fold_map_term bd fm form env in
    let var',  env = bd.unbind_decl ~before:var ~after:var' env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_exists var' form') env
  | Ast.TermForall (var, form) ->
    let var',  env = fold_map_var bd fm var env in
    let var',  env = bd.bind_decl ~before:var ~after:var' env in
    let form', env = fold_map_term bd fm form env in
    let var',  env = bd.unbind_decl ~before:var ~after:var' env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_forall var' form') env
  | Ast.TermMatch (term, list) ->
    let term', env = fold_map_term bd fm term env in
    let list', env =
      List.fold_right
        (fun Ast.{ case_name; case_vars; case_desc; _ } (list, env) ->
           let case_vars', env = fold_map_list (fold_map_var bd fm) case_vars env in
           let case_vars', env = fold_map_list2 bd.bind_decl ~before:case_vars ~after:case_vars' env in
           let case_desc', env = fold_map_term bd fm case_desc env in
           let case_vars', env = fold_map_list2 bd.unbind_decl ~before:case_vars ~after:case_vars' env in
           Ast.mk_case case_name case_vars' case_desc' :: list, env)
        list ([], env)
    in
    fm.fold_map_term ~before ~after:Ast.(mk_term_match term' list') env
  | Ast.TermIte (form, term1, term2) ->
    let form',  env = fold_map_term bd fm form env in
    let term1', env = fold_map_term bd fm term1 env in
    let term2', env = fold_map_term bd fm term2 env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_ite form' term1' term2') env

  | Ast.TermVariadic (vrop, list) ->
    let list', env = fold_map_list (fold_map_term bd fm) list env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_variadic vrop list') env
  | Ast.TermUnop (unop, term) ->
    let term', env = fold_map_term bd fm term env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_unop unop term') env
  | Ast.TermBnop (bnop, term1, term2) ->
    let term1', env = fold_map_term bd fm term1 env in
    let term2', env = fold_map_term bd fm term2 env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_bnop bnop term1' term2') env
  | Ast.TermDefn (fdef, sorts, terms) ->
    let fdef',  env = fold_map_fdef bd fm fdef env in
    let sorts', env = fold_map_list (fold_map_sort bd fm) sorts env in
    let terms', env = fold_map_list (fold_map_term bd fm) terms env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_defn fdef' sorts' terms') env
  | Ast.TermDecl (fdec, sorts, terms) ->
    let fdec',  env = fold_map_fdec bd fm fdec env in
    let sorts', env = fold_map_list (fold_map_sort bd fm) sorts env in
    let terms', env = fold_map_list (fold_map_term bd fm) terms env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_decl fdec' sorts' terms') env

  | Ast.TermConstruct (dttp, sorts, int, terms) ->
    let dttp',  env = fold_map_dttp bd fm dttp env in
    let sorts', env = fold_map_list (fold_map_sort bd fm) sorts env in
    let terms', env = fold_map_list (fold_map_term bd fm) terms env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_construct dttp' sorts' int terms') env
  | Ast.TermSelect (dttp, sorts, int1, int2, term) ->
    let dttp',  env = fold_map_dttp bd fm dttp env in
    let sorts', env = fold_map_list (fold_map_sort bd fm) sorts env in
    let term',  env = fold_map_term bd fm term env in
    fm.fold_map_term ~before ~after:Ast.(mk_term_select dttp' sorts' int1 int2 term') env

  | Ast.ArrayConst (sort, telt) ->
    let sort', env = fold_map_sort bd fm sort env in
    let telt', env = fold_map_term bd fm telt env in
    fm.fold_map_term ~before ~after:Ast.(mk_array_const sort' telt') env
  | Ast.ArrayRead  (sort, tarr, tidx) ->
    let sort', env = fold_map_sort bd fm sort env in
    let tarr', env = fold_map_term bd fm tarr env in
    let tidx', env = fold_map_term bd fm tidx env in
    fm.fold_map_term ~before ~after:Ast.(mk_array_read sort' tarr' tidx') env
  | Ast.ArrayWrite (sort, tarr, tidx, telt) ->
    let sort', env = fold_map_sort bd fm sort env in
    let tarr', env = fold_map_term bd fm tarr env in
    let tidx', env = fold_map_term bd fm tidx env in
    let telt', env = fold_map_term bd fm telt env in
    fm.fold_map_term ~before ~after:Ast.(mk_array_write sort' tarr' tidx' telt') env
  | Ast.ArrayMap (fdef, sorts, terms, tarr) ->
    let fdef',  env = fold_map_fdef bd fm fdef env in
    let sorts', env = fold_map_list (fold_map_sort bd fm) sorts env in
    let terms', env = fold_map_list (fold_map_term bd fm) terms env in
    let tarr',  env = fold_map_term bd fm tarr env in
    fm.fold_map_term ~before ~after:Ast.(mk_array_map fdef' sorts' terms' tarr') env
  | Ast.ArrayDistinct (sort, tarr) ->
    let sort', env = fold_map_sort bd fm sort env in
    let tarr', env = fold_map_term bd fm tarr env in
    fm.fold_map_term ~before ~after:Ast.(mk_array_distinct sort' tarr') env


and fold_map_dttp : type a. a bind -> a fold_map -> Ast.datatype -> a -> Ast.datatype * a =
  fun bd fm (Ast.{ dttp_name; dttp_prms; constructors; _ } as before) env ->
  let dttp_prms', env = fold_map_list2 bd.bind_sort ~before:dttp_prms ~after:dttp_prms env in
  let constructors', env =
    List.fold_right
      (fun Ast.{ cnsr_name; selectors; _ } (list, env) ->
         let selectors', env =
           List.fold_right
             (fun Ast.{ slct_name; slct_sort; _ } (list, env) ->
                let slct_sort', env = fold_map_sort bd fm slct_sort env in
                Ast.mk_selector slct_name slct_sort' :: list, env)
             selectors ([], env)
         in
         Ast.mk_constructor cnsr_name selectors' :: list, env)
      constructors ([], env)
  in
  let dttp_prms', env = fold_map_list2 bd.unbind_sort ~before:dttp_prms ~after:dttp_prms' env in
  fm.fold_map_dttp ~before ~after:Ast.(mk_datatype dttp_name dttp_prms' constructors') env

and fold_map_sdef : type a. a bind -> a fold_map -> Ast.sortdefn -> a -> Ast.sortdefn * a =
  fun bd fm (Ast.{ sdef_name; sdef_prms; sdef_desc; _ } as before) env ->
  let sdef_prms', env = fold_map_list2 bd.bind_sort ~before:sdef_prms ~after:sdef_prms env in
  let sdef_desc', env = fold_map_sort bd fm sdef_desc env in
  let sdef_prms', env = fold_map_list2 bd.unbind_sort ~before:sdef_prms ~after:sdef_prms' env in
  fm.fold_map_sdef ~before ~after:Ast.(mk_sortdefn sdef_name sdef_prms' sdef_desc') env

and fold_map_fdec : type a b. a bind -> a fold_map -> b Ast.fundecl -> a -> b Ast.fundecl * a =
  fun bd fm (Ast.{ fdec_name; fdec_prms; fdec_vars; fdec_desc; _ } as before) env ->
  let fdec_prms', env = fold_map_list2 bd.bind_sort ~before:fdec_prms ~after:fdec_prms env in
  let fdec_vars', env = fold_map_list (fold_map_sort bd fm) fdec_vars env in
  let fdec_desc', env = fold_map_sort bd fm fdec_desc env in
  let fdec_prms', env = fold_map_list2 bd.unbind_sort ~before:fdec_prms ~after:fdec_prms' env in
  fm.fold_map_fdec ~before ~after:Ast.(mk_fundecl fdec_name fdec_prms' fdec_vars' fdec_desc') env

and fold_map_fdef : type a b. a bind -> a fold_map -> b Ast.fundefn -> a -> b Ast.fundefn * a =
  fun bd fm (Ast.{ fdef_name; fdef_prms; fdef_vars; fdef_desc; _ } as before) env ->
  let fdef_prms', env = fold_map_list2 bd.bind_sort ~before:fdef_prms ~after:fdef_prms env in
  let fdef_vars', env = fold_map_list (fold_map_var bd fm) fdef_vars env in
  let fdef_vars', env = fold_map_list2 bd.bind_decl ~before:fdef_vars ~after:fdef_vars' env in
  let fdef_desc', env = fold_map_term bd fm fdef_desc env in
  let fdef_vars', env = fold_map_list2 bd.unbind_decl ~before:fdef_vars ~after:fdef_vars' env in
  let fdef_prms', env = fold_map_list2 bd.unbind_sort ~before:fdef_prms ~after:fdef_prms' env in
  fm.fold_map_fdef ~before ~after:Ast.(mk_fundefn fdef_name fdef_prms' fdef_vars' fdef_desc') env

and fold_map_var : type a. a bind -> a fold_map -> Ast.var -> a -> Ast.var * a =
  fun bd fm ({ var_name; var_sort; _ } as before) env ->
  let var_sort, env = fold_map_sort bd fm var_sort env in
  fm.fold_map_var ~before ~after:Ast.(mk_variable var_name var_sort) env

let fold_map bd fm t env =
  match t with
  | Ast.Sort sdef ->
    let sdef, env = fold_map_sdef bd fm sdef env in
    Ast.Sort sdef, env
  | Ast.Datatype dttp ->
    let dttp, env = fold_map_dttp bd fm dttp env in
    Ast.Datatype dttp, env
  | Ast.Function fdef ->
    let fdef, env = fold_map_fdef bd fm fdef env in
    Ast.Function fdef, env
  | Ast.Predicate fdef ->
    let fdef, env = fold_map_fdef bd fm fdef env in
    Ast.Predicate fdef, env
  | Ast.Query { rela_name; rela_prms; _ } ->
    let rela_prms, env = fold_map_list (fold_map_sort bd fm) rela_prms env in
    Ast.(Query (mk_relation rela_name rela_prms)), env
  | Ast.Relation { rela_name; rela_prms; _ } ->
    let rela_prms, env = fold_map_list (fold_map_sort bd fm) rela_prms env in
    Ast.(Relation (mk_relation rela_name rela_prms)), env
  | Ast.Rule { rule_name; rule_rela; rule_vars; rule_desc; _ } ->
    let rule_vars', env = fold_map_list (fold_map_var bd fm) rule_vars env in
    let rule_vars', env = fold_map_list2 bd.bind_decl ~before:rule_vars ~after:rule_vars' env in
    let rule_desc', env = fold_map_term bd fm rule_desc env in
    let rule_vars', env = fold_map_list2 bd.unbind_decl ~before:rule_vars ~after:rule_vars' env in
    Ast.(Rule (mk_rule rule_name rule_rela rule_vars' rule_desc')), env

module Subst =
struct

  type env =
    (string -> Ast.set Ast.sort) * (Ast.var -> Ast.set Ast.term) * int StringMap.t * int VarMap.t

  let find_string string map =
    try StringMap.find string map
    with _ -> 0

  let incr_string string map =
    let i = find_string string map in
    StringMap.add string (i+1) map

  let decr_string string map =
    let i = find_string string map in
    assert (i > 0);
    StringMap.add string (i-1) map

  let find_var v map =
    try VarMap.find v map
    with _ -> 0

  let incr_var v map =
    let i = find_var v map in
    VarMap.add v (i+1) map

  let decr_var v map =
    let i = find_var v map in
    assert (i > 0);
    VarMap.add v (i-1) map

  let bind = {
    bind_sort   =
      (fun ~before ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, incr_string before sshd, fshd));
    unbind_sort =
      (fun ~before ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, decr_string before sshd, fshd));
    bind_decl   =
      (fun ~before ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, sshd, incr_var before fshd));
    unbind_decl =
      (fun ~before ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, sshd, decr_var before fshd));
    bind_defn   =
      (fun ~before:(v,_) ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, sshd, incr_var v fshd));
    unbind_defn =
      (fun ~before:(v,_) ~after (sfn, ffn, sshd, fshd) ->
         after, (sfn, ffn, sshd, decr_var v fshd));
  }

  let on_sort : type a. (a Ast.sort, env) fn =
    fun ~before:_ ~after (fn, _, shd, _ as env) ->
    match after.Ast.sort_desc with
    | Ast.SortSymbol string ->
      if find_string string shd > 0 then after, env
      else fn string, env
    | _ -> after, env

  let on_term : type a. (a Ast.term, env) fn =
    fun ~before:_ ~after (_, fn, _, shd as env) ->
    match after.Ast.term_desc with
    | Ast.TermVar v ->
      if find_var v shd > 0 then after, env
      else fn v, env
    | _ -> after, env

  let fold_map = {
    fold_map_identity with
    fold_map_sort = on_sort;
    fold_map_term = on_term;
  }

  let eval_sort sfn sort =
    fold_map_sort
      bind fold_map sort (sfn, (fun v -> Ast.mk_term_var v), StringMap.empty, VarMap.empty)
    |> fst

  let eval_term sfn ffn term =
    fold_map_term bind fold_map term (sfn, ffn, StringMap.empty, VarMap.empty)
    |> fst

end

let subst_sort sfn     sort = Subst.eval_sort sfn sort
let subst_term sfn ffn term = Subst.eval_term sfn ffn term

let find_sort smap string =
  match StringMap.find_opt string smap with
  | Some sort -> sort
  | None -> Ast.mk_sort_symbol string

let find_term tmap var =
  match VarMap.find_opt var tmap with
  | Some term -> term
  | None -> Ast.mk_term_var var

let subst_sort_list list sort =
  let smap =
    List.fold_left
      (fun map (string, sort) -> StringMap.add string sort map)
      StringMap.empty list
  in
  subst_sort (find_sort smap) sort

let subst_term_list slist tlist term =
  let smap =
    List.fold_left
      (fun map (string, sort) -> StringMap.add string sort map)
      StringMap.empty slist
  in
  let tmap =
    List.fold_left
      (fun map (var, term) -> VarMap.add var term map)
      VarMap.empty tlist
  in
  subst_term (find_sort smap) (find_term tmap) term

