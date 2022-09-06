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

module Log = Logger.Default
    (struct
      let name = "ast"
    end)

module VarMap = Map.Make
    (struct
      type t = Ast.var
      let compare t1 t2 = compare t1 t2
    end)

(******************************************************************************)

module Vars =
struct

  type env = Ast.var list

  let bind = Ast_utils.bind_identity

  let on_term : type a. (a Ast.term, env) Ast_utils.fn =
    fun ~before:_ ~after env ->
    match after.Ast.term_desc with
    | Ast.TermVar v -> after, v :: env
    | _ -> after, env

  let fold_map = Ast_utils.{
      fold_map_identity with
      fold_map_term = on_term;
    }

  let eval term =
    Ast_utils.fold_map_term bind fold_map term []
    |> snd
    |> List.sort_uniq compare

end

let vars term = Vars.eval term

(******************************************************************************)

module DestructArray =
struct

  let init = ref true

  module FdefHashtbl = Hashtbl.Make
      (struct
        type t = Ast.set Ast.fundefn
        let hash f = f.Ast.fdef_hash
        let equal f1 f2 = Ast.equal f1 f2
      end)

  let table : Ast.set Ast.fundefn FdefHashtbl.t = FdefHashtbl.create 17

  type env = {
    array_size : int;
    fdef_list  : Ast.set Ast.fundefn list;
  }

  let getenv () = {
    array_size = Config.ArraySize.get ();
    fdef_list  = [];
  }

  let selector env sort i =
    if i >= env.array_size
    then Ast.mk_selector "@defaultArray" sort
    else Ast.mk_selector ("@" ^ string_of_int i ^ "Array") sort

  let sort_name = "T"
  let sort = Ast.mk_sort_symbol sort_name

  let array env =
    Ast.(mk_datatype "Array" [sort_name]
           [mk_constructor "Build_Array"
              (List.init (env.array_size + 1) (selector env sort))])

  let construct env list = Ast.mk_term_construct (array env) [sort] 0 list
  let select env arr i = Ast.(mk_term_select (array env) [sort] 0 i (mk_term_var arr))

  let const_name = "const"
  let const env =
    let elt = Ast.mk_variable "e" sort in
    Ast.(mk_fundefn const_name [sort_name] [elt]
           (construct env
              (List.init (env.array_size + 1) (fun _ -> mk_term_var elt))))

  let read_name = "read"
  let read env =
    let arr = Ast.mk_variable "a" (Ast.mk_sort_datatype (array env) [sort]) in
    let idx = Ast.mk_variable "i" Ast.mk_sort_int in
    Ast.(mk_fundefn read_name [sort_name] [ arr; idx ]
           (List.fold_right
              (fun (fm,tm) acc -> mk_term_ite (mk_term_classic fm) tm acc)
              (List.init env.array_size
                 (fun i ->
                    mk_term_equal (mk_term_var idx) (mk_term_int i),
                    select env arr i))
              (select env arr env.array_size)))

  let write_name = "write"
  let write env =
    let arr = Ast.mk_variable "a" (Ast.mk_sort_datatype (array env) [sort]) in
    let idx = Ast.mk_variable "i" Ast.mk_sort_int in
    let elt = Ast.mk_variable "e" sort in
    Ast.(mk_fundefn write_name [sort_name] [ arr; idx; elt ]
           (List.fold_right
              (fun (fm,tm) acc -> mk_term_ite (mk_term_classic fm) tm acc)
              (List.init env.array_size
                 Ast.(fun i ->
                     mk_term_equal (mk_term_var idx) (mk_term_int i),
                     construct env
                       (List.init (env.array_size + 1)
                          (fun j ->
                             if i = j then mk_term_var elt
                             else select env arr j))))
              (mk_term_var arr)))

  let map_name = "<map>"
  let map env fdef slist list =
    let hd,tl =
      let list = List.rev fdef.Ast.fdef_vars in
      List.hd list, List.rev (List.tl list)
    in
    let sort = hd.Ast.var_sort in
    let sres = (Ast.mk_term_defn fdef slist list).Ast.term_sort in
    let arr  = Ast.mk_variable "a" (Ast.mk_sort_datatype (array env) [sort]) in
    let name = map_name ^ fdef.Ast.fdef_name in
    let prms = ["T"; "U"] in
    Ast.(mk_fundefn name prms (tl @ [ arr ])
           (Ast.mk_term_construct (array env) [sres] 0
              (List.init (env.array_size + 1)
                 (fun i ->
                    Ast.mk_term_defn fdef slist
                      (List.map Ast.mk_term_var tl @
                       Ast.[mk_term_select (array env) [sort] 0 i (mk_term_var arr)])))))

  let distinct_name = "distinct"
  let distinct env =
    let arr = Ast.mk_variable "a" (Ast.mk_sort_datatype (array env) [sort]) in
    Ast.(mk_fundefn distinct_name [sort_name] [ arr ]
           (mk_term_distinct
              (List.init (env.array_size + 1) (select env arr))))

  let bind = Ast_utils.bind_identity

  let on_sort : type a. (a Ast.sort, env) Ast_utils.fn =
    fun ~before:_ ~after env ->
    match after.Ast.sort_desc with
    | Ast.SortArray s ->
      Ast.mk_sort_datatype (array env) [s], env
    | _ -> after, env

  let on_term : type a. (a Ast.term, env) Ast_utils.fn =
    fun ~before:_ ~after env ->
    match after.Ast.term_desc with
    | Ast.ArrayConst (s, e) ->
      Ast.(mk_term_defn (const env) [s] [e]), env
    | Ast.ArrayRead (s, a, i) ->
      Ast.(mk_term_defn (read env) [s] [a; i]), env
    | Ast.ArrayWrite (s, a, i, e) ->
      Ast.(mk_term_defn (write env) [s] [a; i; e]), env
    | Ast.ArrayMap (f, slist, list, a) ->
      (match FdefHashtbl.find_opt table f with
       | None ->
         let fdef = map env f slist list in
         FdefHashtbl.add table f fdef;
         Ast.(mk_term_defn fdef (slist @ []) (list @ [a])),
         { env with fdef_list = fdef :: f :: env.fdef_list }
       | Some fdef ->
         Ast.(mk_term_defn fdef (slist @ []) (list @ [a])),
         env)
    | Ast.ArrayDistinct (s, a) ->
      Ast.(mk_term_defn (distinct env) [s] [a]), env
    | _ -> after, env

  let fold_map = Ast_utils.{
      fold_map_identity with
      fold_map_sort = on_sort;
      fold_map_term = on_term;
    }

  let eval t =
    let env = getenv () in
    let t,env = Ast_utils.fold_map bind fold_map t env in
    let maps =
      List.rev_map
        (fun fdef -> Ast.Function fdef)
        env.fdef_list
    in
    if !init then (
      init := false;
      Ast.[
        Datatype (array env);
        Function (const env);
        Function (read  env);
        Function (write env);
      ] @ maps @ [t]
    )
    else
      maps @ [t]

end

let destruct_array t = DestructArray.eval t

(******************************************************************************)

module DestructMatch =
struct

  type env = Ast.var list ref

  let on_form : type a. (a Ast.term, env) Ast_utils.fn =
    fun ~before:_ ~after acc ->
    match after.Ast.term_sort.Ast.sort_desc with
    | Ast.SortProp ->
      (match after.Ast.term_desc with

       | Ast.TermIte (c, t, e) ->
          (Ast.mk_term_or
            (Ast.mk_term_and
               (Ast.mk_term_equal c (Ast.mk_term_bool true))
               t)
            (Ast.mk_term_and
               (Ast.mk_term_equal c (Ast.mk_term_bool false))
               e)), acc

       | Ast.TermMatch (t, list) ->
         (let open Ast in
          match t.term_sort.sort_desc with
          | SortDatatype (d, l) ->
            List.fold_right
              (fun (bds, fm) acc ->
                 mk_term_or
                   (List.fold_right
                      (fun (v, sl) acc -> mk_term_let v sl acc)
                      bds fm)
                   acc)
              (List.mapi
                 (fun i cs ->
                    List.mapi (fun j v -> v, mk_term_select d l i j t) cs.case_vars,
                    mk_term_and
                      (mk_term_equal t
                         (mk_term_construct d l i
                            (List.map (fun v -> mk_term_var v) cs.case_vars)))
                      cs.case_desc)
                 list)
              mk_term_false, acc

          | _ -> after, acc)

       | _ -> after, acc)

    | _ -> after, acc

  let on_rule : type a. (a Ast.term, env) Ast_utils.fn =
    fun ~before:_ ~after acc ->
    match after.Ast.term_sort.Ast.sort_desc with
    | Ast.SortProp ->
      (match after.Ast.term_desc with

       | Ast.TermIte (c, t, e) ->
          (Ast.mk_term_or
            (Ast.mk_term_and
               (Ast.mk_term_equal c (Ast.mk_term_bool true))
               t)
            (Ast.mk_term_and
               (Ast.mk_term_equal c (Ast.mk_term_bool false))
               e)), acc

       | Ast.TermMatch (t, list) ->
         (let open Ast in
          match t.term_sort.sort_desc with
          | SortDatatype (d, l) ->
            List.iter
              (fun cs ->
                 List.iter
                   (fun var ->
                      if not (List.mem var !acc)
                      then acc := var :: !acc)
                   cs.case_vars)
              list;
            List.fold_right
              (fun fm acc -> mk_term_or fm acc)
              (List.mapi
                 (fun i cs ->
                    mk_term_and
                      (mk_term_equal t
                         (mk_term_construct d l i
                            (List.map (fun v -> mk_term_var v) cs.case_vars)))
                      cs.case_desc)
                 list)
              mk_term_false, acc

          | _ -> after, acc)

       | _ -> after, acc)

    | _ -> after, acc

  let bind = Ast_utils.bind_identity

  let fold_map_form = Ast_utils.{
      fold_map_identity with
      fold_map_term = on_form;
    }

  let fold_map_rule = Ast_utils.{
      fold_map_identity with
      fold_map_term = on_rule;
      fold_map_fdef = (fun ~before ~after:_ env -> before, env);
    }

  let eval t =
    match t with
    | Ast.Datatype _ -> t
    | Ast.Function fdef ->
      Ast.Function
        (Ast.mk_fundefn
           fdef.Ast.fdef_name
           fdef.Ast.fdef_prms
           fdef.Ast.fdef_vars
           (Ast_utils.fold_map_term bind fold_map_form fdef.Ast.fdef_desc (ref []) |> fst))
    | Ast.Predicate fdef ->
      Ast.Predicate
        (Ast.mk_fundefn
           fdef.Ast.fdef_name
           fdef.Ast.fdef_prms
           fdef.Ast.fdef_vars
           (Ast_utils.fold_map_term bind fold_map_form fdef.Ast.fdef_desc (ref []) |> fst))
    | Ast.Query _ -> t
    | Ast.Relation _ -> t
    | Ast.Rule rule ->
      let acc = ref (List.rev rule.Ast.rule_vars) in
      let desc = Ast_utils.fold_map_term bind fold_map_rule rule.Ast.rule_desc acc |> fst in
      Ast.Rule
        (Ast.mk_rule
           rule.Ast.rule_name
           rule.Ast.rule_rela
           (List.rev !acc)
           desc)
    | Ast.Sort _ -> t

end

let destruct_match t = [DestructMatch.eval t]

(******************************************************************************)

module UnifyEquality =
struct

  module M = Map.Make
      (struct
        type t = Ast.var
        let compare t1 t2 = compare t1 t2
      end)

  type env = {
    bindings : Ast.set Ast.term M.t;
  }

  let empty = Some { bindings = M.empty }

  let add (v,t) opt =
    if Ast.equal v.Ast.var_sort t.Ast.term_sort
    then
      match opt with
      | None -> None
      | Some env -> Some { bindings = M.add v t env.bindings }
    else
      (Log.Verbose.debug
         ~head:(fun fmt -> fmt "UnifyEquality")
         ~body:(fun fmt -> fmt "%a@\n%a" Ast_pp.pp_var v Ast_pp.pp_term t);
       failwith v.Ast.var_name)

  let find v opt =
    match opt with
    | None -> None
    | Some env -> M.find_opt v env.bindings

  let pick opt =
    match opt with
    | None -> None, opt
    | Some env ->
      match M.choose_opt env.bindings with
      | None -> None, opt
      | Some (key,_) as opt ->
        opt, Some { bindings = M.remove key env.bindings }


  let reset, get, push, flush =
    let cnt = ref (-1) in
    let vars = ref [] in
    (fun () -> cnt := -1; vars := []),
    (fun () -> incr cnt; !cnt),
    (fun v -> vars := v :: !vars),
    (fun () -> let v = !vars in vars := []; v)

  let selector_to_var slct cnt =
    let v =
      Ast.mk_variable
        (Printf.sprintf "%s<%i>" slct.Ast.slct_name cnt)
        slct.Ast.slct_sort
    in
    push v; v

  let select_to_construct d l i1 i2 cnt =
    let list =
      List.map
        (fun sl -> Ast.mk_term_var (selector_to_var sl cnt))
        (Ast_utils.get_constructor d i1).Ast.selectors
    in
    Ast.mk_term_construct d l i1 list, List.nth list i2


  let heuristic v1 v2 =
    let count_char s =
      let cnt = ref 0 in
      String.iter (fun c -> if c = '<' then incr cnt) s;
      !cnt
    in
    count_char v1.Ast.var_name > count_char v2.Ast.var_name
    || String.length v1.Ast.var_name > String.length v2.Ast.var_name
    || String.compare v1.Ast.var_name v2.Ast.var_name > 0


  let rec normalize (t1, t2) env =
    match t1.Ast.term_desc, t2.Ast.term_desc with
    | t1, t2 when Ast.equal t1 t2 -> env

    | Ast.TermVar v1, Ast.TermVar v2 ->
      if heuristic v1 v2 then add (v1, t2) env else add (v2, t1) env

    | Ast.TermVar v1, Ast.TermConstruct _  ->
      if List.mem v1 t2.Ast.term_free then env
      else add (v1, t2) env

    | _, Ast.TermVar _ -> normalize (t2, t1) env

    | Ast.TermSelect (d, l, i1, i2, t), _ ->
      let c, s = select_to_construct d l i1 i2 (get ()) in
      normalize (s, t2) (normalize (t, c) env)

    | _, Ast.TermSelect (d, l, i1, i2, t) ->
      let c, s = select_to_construct d l i1 i2 (get ()) in
      normalize (s, t1) (normalize (t, c) env)

    | Ast.TermConstruct (d1, l1, i1, list1), Ast.TermConstruct (d2, l2,i2, list2) ->
      if d1 = d2 && i1 = i2 && List.for_all2 Ast.equal l1 l2 then
        List.fold_left2
          (fun env t1 t2 -> normalize (t1, t2) env)
          env list1 list2
      else None

    | _, _ -> env

  (*  | Ast.(TermUnop _ | TermBnop _ | TermDecl _ | TermDefn _
            | TermLet _ | TermMatch _ | TermIte _
            | TermConst _ | TermRead _ | TermWrite _ | TermMap _), _
      | _, Ast.(TermUnop _ | TermBnop _ | TermDecl _ | TermDefn _
               | TermLet _ | TermMatch _ | TermIte _
               | TermConst _ | TermRead _ | TermWrite _ | TermMap _)
        -> env

      | _, _ -> None
  *)

  let stabilize env =

    let subst (v1, t1) opt =
      match opt with
      | None -> None
      | Some env ->
        let ssbst s = Ast.mk_sort_symbol s in
        let fsbst v = if Ast.equal v v1 then t1 else Ast.mk_term_var v in
        M.fold
          (fun v2 t2 env ->
             if Ast.equal v1 v2 then (
               if Ast.equal t1 t2
               then env
               else normalize (t1, t2) env)
             else (
               if List.mem v1 t2.Ast.term_free
               then add (v2, Ast_utils.subst_term ssbst fsbst t2) env
               else add (v2, t2) env))
          env.bindings empty
    in

    let rec loop env_in env_out =
      match pick env_in with
      | None, None -> None
      | None, _ -> env_out
      | Some p1, env_in ->
        loop (subst p1 env_in) (add p1 (subst p1 env_out))
    in

    loop env empty


  let rec fixpoint f opt =
    let opt' = f opt in
    match opt, opt' with
    | Some env, Some env' when not (M.equal Ast.equal env.bindings env'.bindings) -> fixpoint f opt'
    | _, _ -> opt'


  let initialize fm : env option =
    let bind = Ast_utils.bind_identity in
    let on_term : type a. (a Ast.term, env option) Ast_utils.fn =
      fun ~before:_ ~after env ->
        match after.Ast.term_desc with
        | Ast.TermSelect (d, l, i1, i2, t') ->
          let c, s = select_to_construct d l i1 i2 (get ()) in
          after, normalize (s, after) (normalize (t', c) env)
        | _ -> after, env
    in
    let fold_map = Ast_utils.{
        fold_map_identity with
        fold_map_term = on_term;
      } in
    Ast_utils.fold_map_term bind fold_map fm empty |> snd

  let extend eq env : env option =
    normalize eq env

  let finalize  env : env option =
    fixpoint stabilize env


  let compute f =

    let rec compute_aux opt f =
      match f.Ast.term_desc with

      | Ast.TermBnop (Imply, f1, f2) ->
        let opt, f1 = compute_aux opt f1 in
        opt, Ast.mk_term_imply f1 f2

      | Ast.TermBnop (And, f1, f2) ->
        let opt, f1 = compute_aux opt f1 in
        let opt, f2 = compute_aux opt f2 in
        opt, Ast.mk_term_and f1 f2

      | Ast.TermBnop (Equal, t1, t2) ->
        (match extend (t1, t2) opt with
         | None -> None, Ast.mk_term_false
         | opt -> opt, Ast.mk_term_equal t1 t2)

      | _ -> opt, f
    in

    let opt, f = compute_aux (initialize f) f in
    match finalize opt with
    | None -> None, Ast.mk_term_true
    | opt -> opt, f


  let subst env t =
    let subst_sort string = Ast.mk_sort_symbol string in
    let subst_term v =
      match find v env with
      | None -> Ast.mk_term_var v
      | Some t -> t
    in
    Ast_utils.subst_term subst_sort subst_term t


  let eval t =
    match t with
    | Ast.Datatype _ -> t
    | Ast.Function _ -> t
    | Ast.Predicate _ -> t
    | Ast.Query _ -> t
    | Ast.Relation _ -> t
    | Ast.Rule rule ->
      reset ();
      let opt, form = compute rule.Ast.rule_desc in
      (match finalize opt with
       | None ->
         Ast.Rule
           (Ast.mk_rule
              rule.Ast.rule_name
              rule.Ast.rule_rela
              rule.Ast.rule_vars
              form)
       | Some _ ->
         let form = subst opt form in
         let vars =
           List.filter (fun v -> List.mem v (vars form)) (flush ())
         in
         Ast.Rule
           (Ast.mk_rule
              rule.Ast.rule_name
              rule.Ast.rule_rela
              (List.append rule.Ast.rule_vars vars)
              form))
    | Ast.Sort _ -> t

end

let unify_equality t = [UnifyEquality.eval t]

(******************************************************************************)

module UnifyEqualityAlt =
struct

  module Vtbl = Hashtbl.Make
      (struct
        type t = Ast.var
        let equal v1 v2 = Ast.equal v1 v2
        let hash v = v.Ast.var_hash
      end)

  module Ttbl = Hashtbl.Make
      (struct
        type t = Ast.set Ast.term
        let equal t1 t2 = Ast.equal t1 t2
        let hash t = t.Ast.term_hash
      end)

  type env = {
    var_to_term : Ast.set Ast.term Vtbl.t option;
    term_to_var : (Ast.set Ast.term * Ast.set Ast.term) Ttbl.t;
  }

  let create n = {
    var_to_term = Some (Vtbl.create n);
    term_to_var = Ttbl.create n;
  }

  let add (v,t) env =
    if Ast.equal v.Ast.var_sort t.Ast.term_sort
    then
      match env.var_to_term with
      | None -> env
      | Some tbl -> Vtbl.replace tbl v t; env
    else failwith v.Ast.var_name

  let find v env =
    match env.var_to_term with
    | None -> None
    | Some tbl -> Vtbl.find_opt tbl v


  let subst env t =
    let subst_sort string = Ast.mk_sort_symbol string in
    let subst_term v =
      match find v env with
      | None -> Ast.mk_term_var v
      | Some t -> t
    in
    Ast_utils.subst_term subst_sort subst_term t


  let reset, get, push, flush =
    let cnt = ref (-1) in
    let vars = ref [] in
    (fun () -> cnt := -1; vars := []),
    (fun () -> incr cnt; !cnt),
    (fun v -> vars := v :: !vars),
    (fun () -> let v = !vars in vars := []; v)

  let selector_to_var slct cnt =
    let v =
      Ast.mk_variable
        (Printf.sprintf "%s<%i>" slct.Ast.slct_name cnt)
        slct.Ast.slct_sort
    in
    push v; v

  let select_to_construct env t d l i1 i2 cnt =
    match Ttbl.find_opt env.term_to_var t with
    | Some _ -> None
    | None ->
      let list =
        List.map
          (fun sl -> Ast.mk_term_var (selector_to_var sl cnt))
          (Ast_utils.get_constructor d i1).Ast.selectors
      in
      let c = Ast.mk_term_construct d l i1 list, List.nth list i2 in
      Ttbl.add env.term_to_var t c; Some c

  let heuristic v1 v2 =
    let count_char s =
      let cnt = ref 0 in
      String.iter (fun c -> if c = '<' then incr cnt) s;
      !cnt
    in
    count_char v1.Ast.var_name > count_char v2.Ast.var_name
    || String.length v1.Ast.var_name > String.length v2.Ast.var_name
    || String.compare v1.Ast.var_name v2.Ast.var_name > 0


  let rec normalize list env =
    match list with
    | (t1, t2) :: list ->
      (match (subst env t1).Ast.term_desc, (subst env t2).Ast.term_desc with
       | t1, t2 when Ast.equal t1 t2 -> normalize list env

       | Ast.TermVar v1, Ast.TermVar v2 ->
         normalize list
           (if heuristic v1 v2 then add (v1, t2) env else add (v2, t1) env)

       | Ast.TermVar v1, Ast.TermConstruct _ ->
         normalize list
           (if List.mem v1 t2.Ast.term_free then env
            else add (v1, t2) env)

       | Ast.TermConstruct _, Ast.TermVar v2 ->
         normalize list
           (if List.mem v2 t1.Ast.term_free then env
            else add (v2, t1) env)

       | Ast.TermSelect (d, l, i1, i2, t), _ ->
         (match select_to_construct env t1 d l i1 i2 (get ()) with
          | Some (c, s) -> normalize ((t, c) :: (s, t2) :: list) env
          | None -> normalize list env)

       | _, Ast.TermSelect (d, l, i1, i2, t) ->
         (match select_to_construct env t2 d l i1 i2 (get ()) with
          | Some (c, s) -> normalize ((t, c) :: (s, t1) :: list) env
          | None -> normalize list env)

       | Ast.TermConstruct (d1, l1, i1, list1), Ast.TermConstruct (d2, l2, i2, list2) ->
         if d1 = d2 && i1 = i2 && List.for_all2 Ast.equal l1 l2 then
           normalize
             (List.fold_left2
                (fun list t1 t2 -> (t1, t2) :: list)
                list list1 list2)
             env
         else { env with var_to_term = None }

       | _, _ -> normalize list env)

    | [] -> env


  let initialize fm : env =
    let bind = Ast_utils.bind_identity in
    let on_term : type a. (a Ast.term, env) Ast_utils.fn =
      fun ~before:_ ~after env ->
        match after.Ast.term_desc with
        | Ast.TermSelect (d, l, i1, i2, t') ->
          (match select_to_construct env after d l i1 i2 (get ()) with
           | Some (c, s) -> after, normalize [(t', c); (s, after)] env
           | None -> after, env)
        | _ -> after, env
    in
    let fold_map = Ast_utils.{
        fold_map_identity with
        fold_map_term = on_term;
      }
    in
    Ast_utils.fold_map_term bind fold_map fm (create 17) |> snd

  let extend eq env : env = normalize [eq] env

  let finalize  env : env = env

  let compute f =

    let rec compute_aux env f =
      match f.Ast.term_desc with

      | Ast.TermBnop (Imply, f1, f2) ->
        let env, f1 = compute_aux env f1 in
        env, Ast.mk_term_imply f1 f2

      | Ast.TermBnop (And, f1, f2) ->
        let env, f1 = compute_aux env f1 in
        let env, f2 = compute_aux env f2 in
        env, Ast.mk_term_and f1 f2

      | Ast.TermBnop (Equal, t1, t2) ->
        let env = extend (t1, t2) env in
        (match env.var_to_term with
         | None -> env, Ast.mk_term_false
         | Some _ -> env, Ast.mk_term_equal t1 t2)

      | _ -> env, f
    in

    let env, f = compute_aux (initialize f) f in
    let env = finalize env in
    match env.var_to_term with
    | None -> env, Ast.mk_term_true
    | Some _ -> env, f


  let eval t =
    match t with
    | Ast.Datatype _ -> t
    | Ast.Function _ -> t
    | Ast.Predicate _ -> t
    | Ast.Query _ -> t
    | Ast.Relation _ -> t
    | Ast.Rule rule ->
      reset ();
      let env, form = compute rule.Ast.rule_desc in
      (match env.var_to_term with
       | None ->
         Ast.Rule
           (Ast.mk_rule
              rule.Ast.rule_name
              rule.Ast.rule_rela
              rule.Ast.rule_vars
              form)
       | Some _ ->
         let form = subst env form in
         let vars =
           List.filter (fun v -> List.mem v (vars form)) (flush ())
         in
         Ast.Rule
           (Ast.mk_rule
              rule.Ast.rule_name
              rule.Ast.rule_rela
              (List.append rule.Ast.rule_vars vars)
              form))
    | Ast.Sort _ -> t

end

let _unify_equality t = [UnifyEqualityAlt.eval t]

(******************************************************************************)

module SplitRule =
struct

  let product f l1 l2 =
    List.rev
      (List.fold_left
         (fun acc x ->
            List.fold_left
              (fun acc y -> f x y :: acc)
              acc l2)
         [] l1)

  let rec split b n f =
    if n > 0 then

      match f.Ast.term_desc with
      | Ast.TermBnop (Imply, f1, f2) ->
        product Ast.mk_term_imply
          (split false (if b then n-1 else n) f1)
          [f2]

      | Ast.TermBnop (And, f1, f2) ->
        product Ast.mk_term_and
          (split false (if b then n-1 else n) f1)
          (split false (if b then n-1 else n) f2)

      | Ast.TermBnop (Or, f1, f2) ->
        List.append (split true n f1) (split true n f2)

      | _ -> [f]

    else [f]

  let eval n t =
    match t with
    | Ast.Datatype _ -> [t]
    | Ast.Function _ -> [t]
    | Ast.Predicate _ -> [t]
    | Ast.Query _ -> [t]
    | Ast.Relation _ -> [t]
    | Ast.Rule rule ->
      List.map
        (fun desc ->
           Ast.Rule (Ast.mk_rule rule.Ast.rule_name rule.Ast.rule_rela rule.Ast.rule_vars desc))
        (split false n rule.Ast.rule_desc)
    | Ast.Sort _ -> [t]

end

let split_rule n t = SplitRule.eval n t

let split_rule t = split_rule t

(******************************************************************************)

let destruct_rule list t =
  match t with
  | Ast.Datatype _ -> [t]
  | Ast.Function _ -> [t]
  | Ast.Predicate _ -> [t]
  | Ast.Query _ -> [t]
  | Ast.Relation _ -> [t]
  | Ast.Rule rule ->
    (match List.assoc_opt rule.Ast.rule_rela list with
     | None -> [t]
     | Some n -> List.concat (List.map (split_rule n) (destruct_match t)))
  | Ast.Sort _ -> [t]

(******************************************************************************)

module RenameVars =
struct

  type env = {
    counters : int StringMap.t;
    bindings : Ast.var list VarMap.t;
  }

  let empty = {
    counters = StringMap.empty;
    bindings = VarMap.empty;
  }

  let find_string string map =
    try StringMap.find string map
    with _ -> 0

  let incr_string string map =
    let i = find_string string map in
    StringMap.add string (i+1) map

  let prefix var =
    if String.contains var.Ast.var_name '<' then
      Some (List.hd (String.split_on_char '<' var.Ast.var_name))
    else None

  let incr_var var map =
    match prefix var with
    | Some name -> incr_string name map
    | None -> map

  let rename env var =
    match prefix var with
    | Some name ->
      Ast.mk_variable
        (Printf.sprintf "%s<%i>" name (find_string name env.counters))
        var.Ast.var_sort
    | None -> var

  let find key env =
    try List.hd (VarMap.find key env.bindings)
    with _ -> key

  let add key var env = {
    counters = incr_var var env.counters;
    bindings =
      VarMap.add key
        (var :: try VarMap.find key env.bindings with _ -> [key])
        env.bindings;
  }

  let remove key env = {
    env with
    bindings =
      VarMap.add key
        (List.tl (VarMap.find key env.bindings))
        env.bindings
  }

  let bind = Ast_utils.{
      bind_identity with
      bind_decl   =
        (fun ~before ~after env ->
           let var = rename env after in
           var, (add before var env));
      unbind_decl =
        (fun ~before ~after env ->
           after, (remove before env));
      bind_defn   =
        (fun ~before:(key,_) ~after:(var,term) env ->
           let var = rename env var in
           (var, term), (add key var env));
      unbind_defn =
        (fun ~before:(key,_) ~after env ->
           after, (remove key env));
    }

  let on_var ~before:_ ~after env =
    find after env, env

  let fold_map = {
    Ast_utils.fold_map_identity with
    fold_map_var = on_var;
  }

  let eval t = [Ast_utils.fold_map bind fold_map t empty |> fst]

end

let rename_vars t = RenameVars.eval t

(******************************************************************************)

module Gensym = struct

  let rename =
    let gensym_counter = ref 100 in
    fun v ->
      incr gensym_counter;
      Ast.(mk_variable (Printf.sprintf "%s<%i>" v.var_name (!gensym_counter)) v.var_sort)

  let find key map =
    try List.hd (VarMap.find key map) with _ -> key

  let add key var map =
    VarMap.add key (var :: try VarMap.find key map with _ -> [key]) map

  let remove key map =
    VarMap.add key (List.tl (VarMap.find key map)) map

  let bind = Ast_utils.{
      bind_identity with
      bind_decl = (fun ~before ~after map ->
          let var = rename after in var, add before var map);
      unbind_decl = (fun ~before ~after map ->
          after, remove before map);
      bind_defn = (fun ~before:(key,_) ~after:(var, term) map ->
          let var = rename var in (var,term), add key var map);
      unbind_defn = (fun ~before:(key,_) ~after map ->
          after, remove key map);
    }
  let on_var ~before:_ ~after map = find after map, map

  (* Replace every variable of t with a fresh one *)
  let eval t =
    Ast_utils.(fold_map bind { fold_map_identity with fold_map_var = on_var} t VarMap.empty)
    |> fst
end


module InlineRelations =
struct

  let _pp_with fn name t =
    let module Log = Logger.Default (struct let name = "inline_relations" end) in
    Log.Verbose.debug ~head:(fun fmt -> fmt "%s" name)
      ~body:(fun fmt -> fmt "%a" fn t)

  let rules = ref []

  let (let*) = Option.bind
  let guard v = if v then Some () else None

  type 'a substitution = (('a Ast.term * 'a Ast.term) list) option

  (* Perform prolog-style unification on TermDecls *)
  let rec unify_decls declA declB optsubst : Ast.set substitution =
    let* subst = optsubst in
    match declA.Ast.term_desc, declB.Ast.term_desc with
    | Ast.TermDecl (fdeclA, slistA, listA), Ast.TermDecl (fdeclB, slistB, listB)
      when String.equal fdeclA.Ast.fdec_name fdeclB.Ast.fdec_name
        && List.for_all2 Ast.equal slistA slistB
      -> unify_all listA listB (Some subst)
    | _ -> None

  and unify_constrs termA termB optsubst =
    let* subst = optsubst in
    match termA.Ast.term_desc, termB.Ast.term_desc with
    | Ast.TermVar vA, Ast.TermVar vB when vA.Ast.var_name = vB.Ast.var_name -> Some subst
    | Ast.TermVar _, _ -> unify_var termA termB subst
    | _, Ast.TermVar _ -> unify_var termB termA subst
    | Ast.TermConstruct (dtA, slistA, idxA, listA), Ast.TermConstruct (dtB, slistB, idxB, listB)
      when Ast.equal dtA dtB && idxA = idxB
           && List.for_all2 Ast.equal slistA slistB
      -> unify_all listA listB (Some subst)
    | _ -> None

  and unify_var var x subst =
    match List.assoc_opt var subst, List.assoc_opt x subst with
    | Some vl, _ -> unify_constrs vl x (Some subst)
    | _, Some vl -> unify_constrs var vl (Some subst)
    | _          -> Some ((var, x) :: subst)

  and unify_all listA listB subst =
    List.fold_left2
      (fun subst vA vB -> unify_constrs vA vB subst)
      subst listA listB

  (* rule_split Imply(a,b) = (b,a) *)
  let rule_split (rule: Ast.rule) : (Ast.prop Ast.term * Ast.prop Ast.term) option =
    match rule.Ast.rule_desc.Ast.term_desc with
    | Ast.TermBnop (Ast.Imply, t1, t2) -> Some (t2, t1)
    | _ -> None

  let rel_name_of_rule (rule: Ast.rule) : string option =
    let* (hd, _) = rule_split rule in
    match hd.Ast.term_desc with
    | Ast.TermDecl (fdecl, _, _) ->
      Some (fdecl.Ast.fdec_name)
    | _ -> failwith "WAT: rule head is not TermDecl!"

  (* add missing variables from term_free in rule_vars *)
  let declare_vars = function
    | Ast.Rule rule ->
      let fv = rule.Ast.rule_desc.Ast.term_free in
      let newvars = List.sort_uniq compare (List.append rule.Ast.rule_vars fv) in
      Ast.Rule (Ast.mk_rule rule.Ast.rule_name rule.Ast.rule_rela newvars rule.Ast.rule_desc)
    | x -> x

  (* apply the inlining to t *)
  let eval rel_names t =

    let bind = Ast_utils.bind_identity in
    let rec fold_map = Ast_utils.{ fold_map_identity with fold_map_term = on_term; }
    and on_term : type a. (a Ast.term, int StringMap.t) Ast_utils.fn =
      fun ~before:_ ~after env ->
        match after.Ast.term_sort.Ast.sort_desc with
        | Ast.SortProp ->
          (match after.Ast.term_desc with
           | Ast.TermDecl (fdecl, _slist, _list) ->
             (* if there is an inlined relation with the same name *)
             (let* reldepth = StringMap.find_opt fdecl.Ast.fdec_name env in
              if reldepth < 0 then
                (* Stop the expansion when we reach the maximum recursion depth *)
                Some (Ast.mk_term_false, env)
              else
                let branches =
                  List.map (fun rule ->
                      let* relname = rel_name_of_rule rule in
                      let* () = guard (relname = fdecl.Ast.fdec_name) in
                      let* renamed_rule = match (Gensym.eval (Ast.Rule rule)) with
                        | Rule r -> Some r | _ -> None in
                      let* (hd, tl) = rule_split renamed_rule in
                      (* unify the head of the rule with the current term *)
                      let* uenv = unify_decls after hd (Some []) in
                      (* recursively expand the body of the matched rule *)
                      (* and decrement the recursion limit *)
                      let exp_tl = Ast_utils.fold_map_term bind fold_map tl
                          (StringMap.add fdecl.Ast.fdec_name (reldepth-1) env)
                                   |> fst in
                      let exp_rule =
                        Ast.mk_rule
                          renamed_rule.rule_name
                          renamed_rule.rule_rela
                          renamed_rule.rule_vars
                          (Ast.mk_term_imply exp_tl hd)
                      in
                      Some (exp_rule, uenv)
                    ) !rules in
                assert (List.exists Stdlib.Option.is_some branches);
                (* Generate an SMT formula from the valid branches *)
                let formula =
                  branches
                  |> List.map (fun branch ->
                      let* (rule, uenv) = branch in
                      let* (_hd, tl) = rule_split rule in
                      (* add equalities in uenv *)
                      Some (List.map (fun (a,b) -> Ast.mk_term_equal a b) uenv
                            |> List.fold_left Ast.mk_term_and Ast.mk_term_true
                            |> Fun.flip Ast.mk_term_and tl))
                  |> List.concat_map Stdlib.Option.to_list (* catMaybes *)
                  |> List.fold_left Ast.mk_term_or Ast.mk_term_false (* join with \/ *)
                in
                (* Replace the current term with the formula *)
                Some (formula,env))
             |> Stdlib.Option.value ~default:(after,env)
           | _ -> after, env)
        | _ -> after, env

    in match t with
    (* Save and remove matching rules *)
    | Ast.Rule r when List.exists (fun (name, _) ->
        (let* relname = rel_name_of_rule r in
         Some (name = relname))
        |> Stdlib.Option.value ~default:false) rel_names ->
      rules := r :: !rules; []
    | Ast.Function _ | Ast.Predicate _ ->
      failwith "Cannot inline a relation inside a definition!"
    | _ ->
      [ Ast_utils.fold_map bind fold_map t
          (List.fold_left (fun m (n, depth) -> StringMap.add n depth m)
             StringMap.empty rel_names)
        |> fst
        |> declare_vars ]
end

let inline_relations rel_names t = InlineRelations.eval rel_names t

(******************************************************************************)

let split_rule t = split_rule max_int t
