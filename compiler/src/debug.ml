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

open Format

module CRD = Context.Rel.Declaration

type env = {
  environ  : Environ.env;
}


let unprintable fmt string =
  fprintf fmt "%s [...]" string

let pp_not_yet_implemented fmt =
  fprintf fmt "[...]"


let pp_print_list pp fmt list =
  pp_print_list
    ~pp_sep:pp_force_newline
    pp fmt list


let pp_name _env fmt (n: Names.Name.t) =
  fprintf fmt "%s"
    ( match n with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id)


let pp_annot_name env fmt bn =
  pp_name env fmt (Context.binder_name bn)


let pp_univ _ fmt (_: Univ.Instance.t) =
  pp_not_yet_implemented fmt


let pp_recursivity_kind _ fmt (r: Declarations.recursivity_kind) =
  fprintf fmt "%s"
    (match r with
     | Declarations.Finite -> "Finite"
     | Declarations.CoFinite -> "CoFinite"
     | Declarations.BiFinite -> "BiFinite")


(******************************************************************************)


let pp_rel env fmt int =
  fprintf fmt "%a"
    (pp_name env) (CRD.get_name (Environ.lookup_rel int env.environ))


let pp_sort _ fmt (s: Sorts.t) =
  fprintf fmt "%s"
    (match Sorts.family s with
     | Sorts.InSProp -> "SProp"
     | Sorts.InProp  -> "Prop"
     | Sorts.InSet   -> "Set"
     | Sorts.InType  -> "Type")


let pp_const _ fmt ((c: Names.Constant.t), _) =
  fprintf fmt "%s" (Names.Constant.to_string c)


let get_inductive_body env (ind: Names.inductive) =
  Inductive.lookup_mind_specif env.environ ind


let pp_inductive env fmt (ind: Names.inductive) =
  let _, oind_body = get_inductive_body env ind in
  fprintf fmt "%s"
    (Names.Id.to_string oind_body.Declarations.mind_typename)


let pp_construct env fmt (((ind: Names.inductive), int), _) =
  let _, oind_body = get_inductive_body env ind in
  fprintf fmt "%s"
    (Names.Id.to_string oind_body.Declarations.mind_consnames.(int-1))


let pp_case_style _ fmt (cs: Constr.case_style) =
  fprintf fmt "%s"
    (match cs with
     | Constr.LetStyle -> "LetStyle"
     | Constr.IfStyle -> "IfStyle"
     | Constr.LetPatternStyle -> "LetPatternStyle"
     | Constr.MatchStyle -> "MatchStyle"
     | Constr.RegularStyle -> "RegularStyle")


let pp_case_info env fmt ci =
  fprintf fmt "@[<1>{ ci_ind: %a; ci_npar: %i; ci_style: %a }@]"
    (pp_inductive env) ci.Constr.ci_ind
    ci.Constr.ci_npar
    (pp_case_style env) ci.Constr.ci_pp_info.Constr.style


let rec pp_constr (env: env) fmt (types: Constr.types) =
  match Constr.kind types with

  | Constr.Rel i ->
    fprintf fmt "@[<1>(Rel %a)@]"
      (pp_rel env) i

  | Constr.Var   _ -> unprintable fmt "Var"
  | Constr.Meta  _ -> unprintable fmt "Meta"
  | Constr.Evar  _ -> unprintable fmt "Evar"

  | Constr.Sort s ->
    fprintf fmt "@[<1>(Sort %a)@]"
      (pp_sort env) s

  | Constr.Cast  _ -> fprintf fmt "Cast"

  | Constr.Prod (bn, t, b) ->
    let environ = Environ.push_rel CRD.(LocalAssum(bn,t)) env.environ in
    fprintf fmt "@[<1>(Prod (%a :@ %a)@ %a@])"
      (pp_annot_name env) bn
      (pp_constr env) t
      (pp_constr { environ }) b

  | Constr.Lambda (bn, t, b) ->
    let environ = Environ.push_rel CRD.(LocalAssum(bn,t)) env.environ in
    fprintf fmt "@[<1>(Lambda (%a :@ %a)@ %a)@]"
      (pp_annot_name env) bn
      (pp_constr env) t
      (pp_constr { environ }) b

  | Constr.LetIn (bn, tm, ty, b) ->
    let environ = Environ.push_rel CRD.(LocalDef(bn,tm,ty)) env.environ in
    fprintf fmt "@[<1>(LetIn (%a %a:@ %a)@ %a@])"
      (pp_annot_name env) bn
      (pp_constr env) tm
      (pp_constr env) ty
      (pp_constr { environ }) b

  | Constr.App (f, array) ->
    fprintf fmt "@[<1>(App %a@\n@[%a@])@]"
      (pp_constr env) f
      (pp_print_list (pp_constr env)) (Array.to_list array)

  | Constr.Const cu ->
    fprintf fmt "@[<1>(Const %a)@]"
      (pp_const env) cu

  | Constr.Ind (ind,_) ->
    fprintf fmt "@[<1>(Ind %a)@]"
      (pp_inductive env) ind

  | Constr.Construct cu ->
    fprintf fmt "@[<1>(Construct %a)@]"
      (pp_construct env) cu

  | Constr.Case  (i,t,_,m,array) ->
    let _, oind_body = get_inductive_body env i.Constr.ci_ind in
    fprintf fmt "@[<1>(Case %a@ %a@ %a@\n%a@]"
      (pp_case_info env) i
      (pp_constr env) m
      (pp_constr env) t
      (pp_print_list (fun fmt (c,i,j,t) ->
           fprintf fmt "| @[<1>(%s %i %i:@ @[%a@])@]"
             (Names.Id.to_string c) i j
             (pp_constr env) t))
      (Array.to_list
         (Array.mapi
            (fun j t ->
               oind_body.Declarations.mind_consnames.(j),
               i.Constr.ci_cstr_ndecls.(j),
               i.Constr.ci_cstr_nargs.(j),
               t)
            array))

  | Constr.Int i ->
    let i = (snd (Uint63.to_int2 i)) in
    fprintf fmt "%d" i

  | Constr.Array _ -> unprintable fmt "Array"
  | Constr.Float _ -> unprintable fmt "Float"
  | Constr.Fix   _ -> unprintable fmt "Fix"
  | Constr.CoFix _ -> unprintable fmt "CoFix"
  | Constr.Proj  _ -> unprintable fmt "Proj"


(******************************************************************************)


let get_constant_body const_body =
  match const_body.Declarations.const_body with
  | Declarations.Undef _ -> None
  | Declarations.Def d ->
    Some (Mod_subst.force_constr d)
  | Declarations.OpaqueDef opaque_def ->
    let force_proof = Opaqueproof.force_proof Library.indirect_accessor in
    let opaque_tables = Global.opaque_tables () in
    let constr, _ = force_proof opaque_tables opaque_def in
    Some constr
  | Declarations.Primitive _ -> assert false


let pp_toplevel_const_body env fmt
    (const_body: Opaqueproof.opaque Declarations.constant_body) =
  let const_type = const_body.Declarations.const_type in
  match get_constant_body const_body with
  | None -> fprintf fmt "%a" (pp_constr env) const_type
  | Some c ->
    fprintf fmt "@[<1>%a :@ @[%a@]@]"
      (pp_constr env) c
      (pp_constr env) const_type


let pp_toplevel_const env fmt ((c: Names.Constant.t), u) =
  let const_body = Environ.lookup_constant c env.environ in
  fprintf fmt "@[<1>(%s, %a@\n%a)@]"
    (Names.Constant.to_string c)
    (pp_univ env) u
    (pp_toplevel_const_body env) const_body


let pp_toplevel_inductive_body env fmt ((_ind,u as pind), (_mind,oind as specif)) =
  let mind_type = Inductive.type_of_inductive (specif, u) in
  fprintf fmt "@[%s %i %i: %a :=@\n%a@]"
    (Names.Id.to_string oind.Declarations.mind_typename)
    oind.Declarations.mind_nrealargs
    oind.Declarations.mind_nrealdecls
    (pp_constr env) mind_type
    (pp_print_list (fun fmt (c,i,j,t) ->
         fprintf fmt "| @[<1>(%s %i %i :@ @[%a@])@]"
           (Names.Id.to_string c) i j
           (pp_constr env) t))
    (Array.to_list
       (Array.mapi
          (fun i t ->
             oind.Declarations.mind_consnames.(i),
             oind.Declarations.mind_consnrealargs.(i),
             oind.Declarations.mind_consnrealdecls.(i),
             t)
          (Inductive.arities_of_specif pind specif)))


let pp_toplevel_inductive env fmt ((ind,int), u) =
  let list =
    try
      Array.to_list (Inductiveops.compute_projections env.environ (ind,int))
    with _ -> []
  in
  let mind = Environ.lookup_mind ind env.environ in
  fprintf fmt "@[@[<1>{ %s %i %a@\n mind_finite: %a@\n mind_nparams: %i@\n mind_nparams_rec: %i }@]@\n@[<1>[%a]@]@]@\n%a"
    (Names.MutInd.to_string ind) int (pp_univ env) u
    (pp_recursivity_kind env) mind.Declarations.mind_finite
    mind.Declarations.mind_nparams
    mind.Declarations.mind_nparams_rec
    (pp_print_list (fun fmt (t1,t2) -> fprintf fmt "@[<1>(%a,@\n%a)@]" (pp_constr env) t1 (pp_constr env) t2)) list
    (pp_print_list (pp_toplevel_inductive_body env))
    (Array.to_list
       (Array.map
          (fun oind -> (ind,u), (mind,oind))
          mind.mind_packets))


let pp_toplevel_constr (env: env) fmt (types: Constr.types) =
  match Constr.kind types with

  | Constr.Const cu ->
    fprintf fmt "@[<1>(Const %a)@]"
      (pp_toplevel_const env) cu

  | Constr.Ind iu ->
    fprintf fmt "@[<1>(Ind %a)@]"
      (pp_toplevel_inductive env) iu

  | _ -> pp_constr env fmt types


(******************************************************************************)


let pp_constr fmt t =
  fprintf fmt "%a"
    (pp_toplevel_constr { environ = Global.env () }) t


let pp_constrexpr fmt (def: Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Constrintern.interp_constr env sigma def |> fst
  |> EConstr.to_constr sigma
  |> fprintf fmt "%a" (pp_toplevel_constr { environ = env })

