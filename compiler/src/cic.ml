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
      let name = "cic"
    end)

type recursivity_kind = Declarations.recursivity_kind =
  | Finite
  | CoFinite
  | BiFinite

type sort = Prop | Set | Type

type term = {
  term_hash : int;
  term_desc : term_desc;
}

and term_desc =
  | Rel       of name
  | Sort      of sort
  | Product   of name * typ * typ
  | Lambda    of name * typ * term
  | LetIn     of name * term * typ * term
  | App       of term * term array
  | Constant  of constant
  | Inductive of (inductive * int)
  | Construct of (inductive * int) * int
  | Project   of projection * term
  | Case      of case * term * typ * term array
  | Int       of int
  | Float     of float
  | Array     of term array * term * typ
  | Primitive of Primitive.t * typ

and typ = term

and constant = {
  cnst_hash : int;
  cnst_ident: ident;
  cnst_type : typ;
  cnst_body : term option;
}

and inductive = {
  indv_hash  : int;
  indv_ident : ident;
  mutable indv_body : mutual_inductive;
}

and mutual_inductive = {
  mind_hash      : int;
  mind_finite    : recursivity_kind;
  mind_npars     : int;
  mind_npars_rec : int;
  mind_bodies    : one_inductive array;
}

and one_inductive = {
  oind_hash  : int;
  oind_name  : string;
  oind_type  : typ;
  oind_nargs : int;
  oind_ndecls: int;
  oind_ctors : constructor array;
  oind_projs : (string * term * typ) array;
}

and constructor = {
  ctor_hash  : int;
  ctor_name  : string;
  ctor_type  : typ;
  ctor_nargs : int;
  ctor_ndecls: int;
}

and projection = {
  proj_hash  : int;
  proj_indv  : inductive * int;
  proj_name  : string;
  proj_npars : int;
  proj_arg   : int;
}

and case = {
  case_hash  : int;
  case_ndecls: int array;
  case_nargs : int array;
  case_indv  : inductive * int;
}


(******************************************************************************)

let get_inductive_body ({ indv_body; _ }, int) =
  indv_body, indv_body.mind_bodies.(int)

let get_projection_body { proj_indv; proj_arg; _ } =
  (get_inductive_body proj_indv |> snd).oind_projs.(proj_arg)


let rec pp_term fmt term =
  match term.term_desc with
  | Rel nm -> Format.fprintf fmt "@[<hov 1>(Rel %a)@]" Name.pp nm
  | Sort st ->
    Format.fprintf fmt "@[<hov 1>(Sort %s)@]"
      (match st with
       | Prop -> "Prop"
       | Set  -> "Set"
       | Type -> "Type")
  | Product (nm, ty, bd) ->
    Format.fprintf fmt "@[<hov 1>(Product %a@ %a@ %a)@]"
      Name.pp nm
      pp_term ty
      pp_term bd
  | Lambda (nm, tm, bd) ->
    Format.fprintf fmt "@[<hov 1>(Lambda %a@ %a@ %a)@]"
      Name.pp nm
      pp_term tm
      pp_term bd
  | LetIn (nm, ty, tm, bd) ->
    Format.fprintf fmt "@[<hov 1>(LetIn %a@ %a@ %a@ %a)@]"
      Name.pp nm
      pp_term ty
      pp_term tm
      pp_term bd
  | App (fn, array) ->
    Format.fprintf fmt "@[<hov 1>(App@ %a@ [@[%a@]])@]"
      pp_term fn
      (Format.pp_print_list pp_term) (Array.to_list array)
  | Constant cn -> Format.fprintf fmt "@[<hov 1>(Constant %s)@]" (fst cn.cnst_ident)
  | Inductive iv ->
    let _, oind = get_inductive_body iv in
    Format.fprintf fmt "@[<hov 1>(Inductive %s)@]" oind.oind_name
  | Construct (iv, int) ->
    let _, oind = get_inductive_body iv in
    Format.fprintf fmt "@[<hov 1>(Construct %s)@]" oind.oind_ctors.(int).ctor_name
  | Project (pj, tm) ->
    Format.fprintf fmt "@[<hov 1>(Project %s@ %a)@]"
      pj.proj_name
      pp_term tm
  | Case (_, tm, ty, array) ->
    Format.fprintf fmt "@[<hov 1>(Case@ %a@ %a@ [@[%a@]])@]"
      pp_term tm
      pp_term ty
      (Format.pp_print_list pp_term) (Array.to_list array)
  | Int int -> Format.fprintf fmt "@[<hov 1>(Int %i)@]" int
  | Float float -> Format.fprintf fmt "@[<hov 1>(Float %f)@]" float
  | Array (array, tm, ty) ->
    Format.fprintf fmt "@[<hov 1>(Array@ [@[%a@]]@ %a@ %a)@]"
      (Format.pp_print_list pp_term) (Array.to_list array)
      pp_term tm
      pp_term ty
  | Primitive (pm, ty) ->
    Format.fprintf fmt "@[<hov 1>(Primitive %s@ %a)@]"
      (Primitive.to_string pm)
      pp_term ty


let pp_constructor : Format.formatter -> constructor -> unit =
  fun fmt { ctor_name; ctor_type; ctor_nargs; _ } ->
  Format.fprintf fmt "@[<hov 1>{ctor_name: %s@\nctor_nargs: %i@\nctor_type:@ %a}@]"
    ctor_name ctor_nargs
    pp_term ctor_type

let pp_one_inductive : Format.formatter -> one_inductive -> unit =
  fun fmt { oind_name; oind_type; oind_ctors; oind_projs; _ } ->
  Format.fprintf fmt "@[<hov 1>{oind_name: %s@\noind_type:@ %a@\noind_ctors:@ [@[%a@]]@\noind_projs:@ [@[%a@]]}@]"
    oind_name
    pp_term oind_type
    (Format.pp_print_list pp_constructor) (Array.to_list oind_ctors)
    (Format.pp_print_list (fun fmt (string,typ,term) ->
         Format.fprintf fmt "@[<1>(%s,@\n%a,@\n%a)@]" string pp_term typ pp_term term))
    (Array.to_list oind_projs)

let pp_mutual_inductive : Format.formatter -> mutual_inductive -> unit =
  fun fmt { mind_npars; mind_bodies; _ } ->
  Format.fprintf fmt "@[<hov 1>{mind_npars: %i@\nmind_bodies:@ [@[%a@]]}@]"
    mind_npars
    (Format.pp_print_list pp_one_inductive) (Array.to_list mind_bodies)

let pp_inductive : Format.formatter -> inductive -> unit =
  fun fmt { indv_ident; indv_body; _ } ->
  Format.fprintf fmt "@[<hov 1>{indv_ident: %a@\nindv_body:@ %a}@]"
    pp_ident indv_ident
    pp_mutual_inductive indv_body


let terms_hash array = Array.map (fun tm -> tm.term_hash) array


let mk_term term_desc =
  let term_hash =
    match term_desc with
    | Rel string -> Hashtbl.hash ("Rel", string)
    | Sort st -> Hashtbl.hash ("Sort", st)
    | Product (nm, tp, bd) ->
      Hashtbl.hash ("Product", nm, tp.term_hash, bd.term_hash)
    | Lambda (nm, tp, bd) ->
      Hashtbl.hash ("Lambda", nm, tp.term_hash, bd.term_hash)
    | LetIn (nm, tm, tp, bd) ->
      Hashtbl.hash ("LetIn", nm, tm.term_hash, tp.term_hash, bd.term_hash)
    | App (tm, array) ->
      Hashtbl.hash ("App", tm.term_hash, terms_hash array)
    | Constant cn -> Hashtbl.hash ("Constant", cn.cnst_hash)
    | Inductive (ind,int) -> Hashtbl.hash ("Inductive", ind.indv_hash, int)
    | Construct ((ind,int1),int2) -> Hashtbl.hash ("Construct", ind.indv_hash, int1, int2)
    | Project (proj,tm) -> Hashtbl.hash ("Project", proj.proj_hash, tm.term_hash)
    | Case (cs, tm, tp, array) ->
      Hashtbl.hash ("Case", cs.case_hash, tm.term_hash, tp.term_hash, terms_hash array)
    | Int int -> Hashtbl.hash ("Int", int)
    | Float float -> Hashtbl.hash ("Float", float)
    | Array (array, tm, tp) -> Hashtbl.hash ("Array", terms_hash array, tm.term_hash, tp.term_hash)
    | Primitive (prim, tp) -> Hashtbl.hash ("Primitive", prim, tp.term_hash)
  in
  { term_hash; term_desc }


let mk_constant cnst_ident cnst_type cnst_body =
  let cnst_hash =
    Hashtbl.hash
      (cnst_ident,
       (match cnst_body with
        | None -> None
        | Some tm -> Some tm.term_hash),
       cnst_type.term_hash)
  in
  { cnst_hash; cnst_ident; cnst_type; cnst_body }


let mk_inductive indv_ident indv_body =
  let indv_hash = Hashtbl.hash (indv_ident, indv_body.mind_hash) in
  { indv_hash; indv_ident; indv_body }


let mk_mutual_inductive_body mind_finite mind_npars mind_npars_rec mind_bodies =
  let mind_hash =
    Hashtbl.hash (mind_finite, mind_npars, mind_npars_rec,
                  Array.map (fun oind -> oind.oind_hash) mind_bodies)
  in
  { mind_hash; mind_finite; mind_npars; mind_npars_rec; mind_bodies }


let mk_one_inductive_body oind_name oind_type oind_nargs oind_ndecls oind_ctors oind_projs =
  let oind_hash =
    Hashtbl.hash (oind_name, oind_type.term_hash, oind_nargs, oind_ndecls,
                  Array.map (fun ctor -> ctor.ctor_hash) oind_ctors,
                  Array.map (fun (string,term,typ) -> string, term.term_hash, typ.term_hash) oind_projs)
  in
  { oind_hash; oind_name; oind_type; oind_nargs; oind_ndecls; oind_ctors; oind_projs }


let mk_constructor ctor_name ctor_type ctor_nargs ctor_ndecls =
  let ctor_hash =
    Hashtbl.hash (ctor_name, ctor_type.term_hash, ctor_nargs)
  in
  { ctor_hash; ctor_name; ctor_type; ctor_nargs; ctor_ndecls }


let mk_projection (indv,int as proj_indv) proj_name proj_npars proj_arg =
  let proj_hash =
    Hashtbl.hash (proj_name, indv.indv_hash, int, proj_npars, proj_arg)
  in
  { proj_hash; proj_name; proj_indv; proj_npars; proj_arg }


let mk_case case_ndecls case_nargs (indv,int as case_indv) =
  let case_hash =
    Hashtbl.hash (case_ndecls, case_nargs, indv.indv_hash, int)
  in
  { case_hash; case_ndecls; case_nargs; case_indv }


(******************************************************************************)


module CRD = Context.Rel.Declaration

type env = {
  environ : Environ.env;
  projs : StringSet.t;
  cache : inductive StringHashtbl.t;
}

let extract_name name =
  match name with
  | Names.Name.Anonymous -> Name.Anonymous
  | Names.Name.Name id -> Name.of_string (Names.Id.to_string id)

let extract_name_from_annot_name annot_name =
  extract_name (Context.binder_name annot_name)

let convert_name = function
  | Name.Anonymous -> Names.Name.Anonymous
  | nm -> Names.Name.mk_name (Names.Id.of_string_soft Name.(to_string nm))

let fresh_annot_name env anm =
  match Context.binder_name anm with
  | Names.Name.Anonymous -> anm
  | Names.Name.Name id ->
    if StringSet.mem (Names.Id.to_string id) env.projs then anm
    else
      let relevance = Context.binder_relevance anm in
      let name = convert_name (Name.fresh ()) in
      Context.make_annot name relevance

let get_constant_body cn =
  match cn.Declarations.const_body with
  | Declarations.Undef _ -> None
  | Declarations.Def d -> Some (Mod_subst.force_constr d)
  | Declarations.OpaqueDef _ -> None
  | Declarations.Primitive _ -> assert false

let is_primitive cn =
  match cn.Declarations.const_body with
  | Declarations.Primitive pm ->
    (match pm with
     | CPrimitives.Int63add    -> Some Primitive.IntAdd
     | CPrimitives.Int63sub    -> Some Primitive.IntSub
     | CPrimitives.Int63mul    -> Some Primitive.IntMul
     | CPrimitives.Int63div    -> Some Primitive.IntDiv
     | CPrimitives.Int63mod    -> Some Primitive.IntMod
     | CPrimitives.Int63eq     -> Some Primitive.IntEq
     | CPrimitives.Int63lt     -> Some Primitive.IntLt
     | CPrimitives.Int63le     -> Some Primitive.IntLe
     | CPrimitives.Float64add  -> Some Primitive.FloatAdd
     | CPrimitives.Float64sub  -> Some Primitive.FloatSub
     | CPrimitives.Float64mul  -> Some Primitive.FloatMul
     | CPrimitives.Float64div  -> Some Primitive.FloatDiv
     | CPrimitives.Float64abs  -> Some Primitive.FloatAbs
     | CPrimitives.Float64sqrt -> Some Primitive.FloatSqrt
     | CPrimitives.Float64eq   -> Some Primitive.FloatEq
     | CPrimitives.Float64lt   -> Some Primitive.FloatLt
     | CPrimitives.Float64le   -> Some Primitive.FloatLe
     | CPrimitives.Arraymake   -> Some Primitive.ArrayMake
     | CPrimitives.Arraydefault-> Some Primitive.ArrayDefault
     | CPrimitives.Arrayget    -> Some Primitive.ArrayGet
     | CPrimitives.Arrayset    -> Some Primitive.ArraySet
     | CPrimitives.Arraycopy   -> Some Primitive.ArrayCopy
     | CPrimitives.Arraylength -> Some Primitive.ArrayLength
     | _ -> assert false)
  | _ -> None

let rec extract_term (env: env) (types: Constr.types) =
  match Constr.kind types with

  | Constr.Rel int ->
    let nm = CRD.get_name (Environ.lookup_rel int env.environ) in
    Ok (mk_term (Rel (extract_name nm)))

  | Constr.Var  _ -> failure (fun _ -> "Unextractable term Var")
  | Constr.Meta _ -> failure (fun _ -> "Unextractable term Meta")
  | Constr.Evar _ -> failure (fun _ -> "Unextractable term Evar")

  | Constr.Sort st ->
    let st =
      match Sorts.family st with
      | Sorts.InSProp-> Prop
      | Sorts.InProp -> Prop
      | Sorts.InSet  -> Set
      | Sorts.InType -> Type
    in
    Ok (mk_term (Sort st))

  | Constr.Cast _ -> failure (fun _ -> "Unextractable term Cast")

  | Constr.Prod (anm, tp, bd) ->
    let anm = fresh_annot_name env anm in
    let environ = Environ.push_rel CRD.(LocalAssum(anm, tp)) env.environ in
    let nm = (extract_name_from_annot_name anm) in
    extract_typ env tp >>= fun tp ->
    extract_typ { env with environ } bd >>= fun bd ->
    Ok (mk_term (Product (nm, tp, bd)))

  | Constr.Lambda (anm, tp, bd) ->
    let anm = fresh_annot_name env anm in
    let environ = Environ.push_rel CRD.(LocalAssum(anm, tp)) env.environ in
    let nm = (extract_name_from_annot_name anm) in
    extract_typ env tp >>= fun tp ->
    extract_term { env with environ } bd >>= fun bd ->
    Ok (mk_term (Lambda (nm, tp, bd)))

  | Constr.LetIn (anm, tm, tp, bd) ->
    let anm = fresh_annot_name env anm in
    let environ = Environ.push_rel CRD.(LocalDef(anm, tm, tp)) env.environ in
    let nm = (extract_name_from_annot_name anm) in
    extract_term env tm >>= fun tm ->
    extract_typ env tp >>= fun tp ->
    extract_term { env with environ } bd >>= fun bd ->
    Ok (mk_term (LetIn (nm, tm, tp, bd)))

  | Constr.App (tm, array) ->
    extract_term env tm >>= fun tm ->
    Result.Array.map (extract_term env) array >>= fun array ->
    Ok (mk_term (App (tm, array)))

  | Constr.Const (cn, _) -> extract_constant env cn

  | Constr.Ind (ind, _) ->
    extract_inductive env ind >>= fun (iv,int as ind) ->
    let oind = try iv.indv_body.mind_bodies.(int) with _ -> assert false in
    (match Primitive.string_to_relation oind.oind_name with
     | Some pm -> Ok (mk_term (Primitive (Primitive.Relation pm, oind.oind_type)))
     | None -> Ok (mk_term (Inductive ind)))

  | Constr.Construct ((ind, int),_) ->
    extract_inductive env ind >>= fun (iv,i as ind) ->
    let oind = iv.indv_body.mind_bodies.(i) in
    let ctor = oind.oind_ctors.(int-1) in
    (match Primitive.string_to_relation oind.oind_name, ctor.ctor_name with
     | Some _, _ -> failure (fun _ -> "Constructor of a relation, proofs should be erased")
     | None, _ -> Ok (mk_term (Construct (ind,int-1))))

  | Constr.Proj (proj, tm) ->
    let ind   = Names.Projection.inductive proj in
    let npars = Names.Projection.npars proj in
    let arg   = Names.Projection.arg   proj in
    let name  = Names.(Label.to_string (Projection.label proj)) in
    extract_inductive env ind >>= fun ind ->
    extract_term env tm >>= fun tm ->
    Ok (mk_term (Project (mk_projection ind name npars arg, tm)))

  | Constr.Case (cs, tp, _, tm, array) ->
    (* TODO: Deal with parameters *)
    extract_case env cs >>= fun cs ->
    extract_typ  env tp >>= fun tp ->
    extract_term env tm >>= fun tm ->
    Result.Array.map (extract_term env) array >>= fun array ->
    Ok (mk_term (Case (cs, tm, tp, array)))

  | Constr.Int int ->
    let int = (snd (Uint63.to_int2 int)) in
    Ok (mk_term (Int int))

  | Constr.Float float ->
    let float = Uint63.to_float (Float64.normfr_mantissa float) in
    Ok (mk_term (Float float))

  | Constr.Array (_,array, tm, tp) ->
    Result.Array.map (extract_term env) array >>= fun array ->
    extract_term env tm >>= fun tm ->
    extract_typ env tp >>= fun tp ->
    Ok (mk_term (Array (array, tm, tp)))

  | Constr.Fix   _ -> failure (fun _ -> "Unextractable term Fix")
  | Constr.CoFix _ -> failure (fun _ -> "Unextractable term CoFix")


and extract_typ env types = extract_term env types


and extract_inductive env (ind,int as i) =
  let ident = kername_to_ident (Names.MutInd.canonical ind) in
  let string = ident_to_string ident in
  match StringHashtbl.find_opt env.cache string with
  | Some indv -> Ok (indv,int)
  | None ->
    let mind = Environ.lookup_mind ind env.environ in
    extract_mutual_inductive extract_dummy_one_inductive env i mind >>= fun mutind ->
    let indv = mk_inductive ident mutind in
    StringHashtbl.add env.cache string indv;
    let env = { env with
                environ =
                  Environ.push_rel_context
                    (Inductive.inductive_paramdecls (mind, Univ.Instance.empty))
                    env.environ;
              } in
    extract_mutual_inductive extract_one_inductive env i mind >>= fun mutind ->
    indv.indv_body <- mutind;
    Log.Verbose.debug
      ~head:(fun fmt -> fmt "extract_inductive")
      ~body:(fun fmt -> fmt "%a" pp_inductive indv);
    Ok (indv,int)


and extract_mutual_inductive f env ind mind =
  let mind_finite = mind.Declarations.mind_finite in
  let mind_npars  = mind.Declarations.mind_nparams in
  let mind_npars_rec = mind.Declarations.mind_nparams_rec in
  Result.Array.map (f env ind mind) mind.Declarations.mind_packets >>= fun mind_bodies ->
  Ok (mk_mutual_inductive_body mind_finite mind_npars mind_npars_rec mind_bodies)


and extract_dummy_one_inductive env _ind mind oind =
  let oind_name = Names.Id.to_string oind.Declarations.mind_typename in
  extract_term env (Inductive.type_of_inductive ((mind,oind),Univ.Instance.empty))
  >>= fun oind_type ->
  Ok (mk_one_inductive_body oind_name oind_type
        oind.Declarations.mind_nrealargs
        oind.Declarations.mind_nrealdecls
        [||] [||])


and extract_one_inductive env (ind,_ as i) mind oind =
  let oind_name = Names.Id.to_string oind.Declarations.mind_typename in
  extract_term env (Inductive.type_of_inductive ((mind,oind),Univ.Instance.empty))
  >>= fun oind_type ->
  Result.Array.map
    (fun (proj, (term, typ)) ->
       let string = Names.(Label.to_string (Projection.Repr.label proj)) in
       extract_term env term >>= fun term ->
       extract_term env typ  >>= fun typ  ->
       Ok (string, term, typ))
    (match Declareops.inductive_make_projections i mind with
     | None -> [||]
     | Some array ->
       Array.map2 (fun x y -> x,y) array (Inductiveops.compute_projections env.environ i))
  >>= fun oind_projs ->
  let env = {
    env with
    projs = Array.fold_left (fun set (string,_,_) -> StringSet.add string set) env.projs oind_projs;
  } in
  Result.Array.map2
    (fun term (string, nargs, ndecls) ->
       extract_term env term >>= fun term ->
       Ok (mk_constructor string term nargs ndecls))
    (Inductive.arities_of_specif (ind,Univ.Instance.empty) (mind,oind))
    (Array.mapi
       (fun int id ->
          Names.Id.to_string id,
          oind.Declarations.mind_consnrealargs.(int),
          oind.Declarations.mind_consnrealdecls.(int))
       oind.Declarations.mind_consnames)
  >>= fun oind_ctors ->
  Ok (mk_one_inductive_body oind_name oind_type
        oind.Declarations.mind_nrealargs
        oind.Declarations.mind_nrealdecls
        oind_ctors oind_projs)


and extract_case env cs =
  let ndecls = cs.Constr.ci_cstr_ndecls in
  let nargs  = cs.Constr.ci_cstr_nargs in
  extract_inductive env cs.Constr.ci_ind >>= fun ind ->
  Ok (mk_case ndecls nargs ind)


and extract_constant env cn =
  let kn = Names.Constant.canonical cn in
  let cn = Environ.lookup_constant cn env.environ in
  extract_typ env cn.Declarations.const_type >>= fun tp ->
  match is_primitive cn with
  | Some pm -> Ok (mk_term (Primitive (Primitive.Constant pm, tp)))
  | None ->
    let ident = kername_to_ident kn in
    match ident with
    | "not", ["Logic"; "Init"; "Coq"]-> Ok (mk_term Primitive.(Primitive (Relation Not, tp)))
    | "le",  ["Peano"; "Init"; "Coq"]-> Ok (mk_term Primitive.(Primitive (Relation Le, tp)))
    | "lt",  ["Peano"; "Init"; "Coq"]-> Ok (mk_term Primitive.(Primitive (Relation Lt, tp)))
    | "ge",  ["Peano"; "Init"; "Coq"]-> Ok (mk_term Primitive.(Primitive (Relation Ge, tp)))
    | "gt",  ["Peano"; "Init"; "Coq"]-> Ok (mk_term Primitive.(Primitive (Relation Gt, tp)))
    | "const" ,  ["Array"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Constant ArrayMake, tp)))
    | "select",  ["Array"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Constant ArrayGet, tp)))
    | "store" ,  ["Array"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Constant ArraySet, tp)))
    | "map"   ,  ["Array"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Constant ArrayMap, tp)))
    | "distinct",["Array"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Relation ArrayDistinct, tp)))
    | "eqb",  ["Equality"; "Extractor"]-> Ok (mk_term Primitive.(Primitive (Constant Eqb, tp)))
    | _ ->
      Result.Option.map (extract_term env) (get_constant_body cn) >>= fun opt ->
      match opt with
      | None -> Ok (mk_term (Constant (mk_constant ident tp opt)))
      | Some bd ->
        if Config.InlinedConstants.mem kn then Ok bd
        else Ok (mk_term (Constant (mk_constant ident tp opt)))


(******************************************************************************)


let log_debug env sigma constr =
  let module Coq = Logger.Default(struct let name = "coq" end) in
  let pp =
    (match Constr.kind constr with
     | Constr.Const (cn, _) ->
       let tp, bd =
         let cn = Environ.lookup_constant cn env in
         cn.Declarations.const_type, get_constant_body cn
       in
       let pp = Names.Constant.print cn in
       (match bd with
        | None ->
          Coq.Verbose.debug
            ~head:(fun fmt -> fmt "%a" Pp.pp_with pp)
            ~body:(fun fmt -> fmt "%a" Pp.pp_with (Printer.pr_constr_env env sigma tp))
        | Some bd ->
          Coq.Verbose.debug
            ~head:(fun fmt -> fmt "%a" Pp.pp_with pp)
            ~body:(fun fmt -> fmt "%a\ :\ %a"
                      Pp.pp_with (Printer.pr_constr_env env sigma bd)
                      Pp.pp_with (Printer.pr_constr_env env sigma tp)));
       pp

     | Constr.Ind ((ind, _),_) ->
       let mind = Environ.lookup_mind ind env in
       let pp = Names.MutInd.print ind in
       Coq.Verbose.debug
         ~head:(fun fmt -> fmt "%a" Pp.pp_with pp)
         ~body:(fun fmt -> fmt "%a" Pp.pp_with (Printmod.pr_mutual_inductive_body env ind mind None));
       pp

     | _ ->
       Coq.debug
         (fun fmt -> fmt "%a" Pp.pp_with (Printer.pr_constr_env env sigma constr));
       Pp.str ""
    )
  in
  Coq.Verbose.debug
    ~head:(fun fmt -> fmt "%a" Pp.pp_with pp)
    ~body:(fun fmt -> fmt "%a" Debug.pp_constr constr)

let extract (def: Constrexpr.constr_expr) : (term, exn) result =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let constr =
    Constrintern.interp_constr env sigma def |> fst
    |> EConstr.to_constr sigma
  in log_debug env sigma constr;
  extract_term { environ = env; projs = StringSet.empty; cache = StringHashtbl.create 17 } constr

