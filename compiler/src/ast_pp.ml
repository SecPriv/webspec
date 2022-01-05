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

let pp_print_list pp fmt list =
  pp_print_list
    ~pp_sep:pp_force_newline
    pp fmt list

let rec pp_sort : type a. formatter -> a Ast.sort -> unit =
  fun fmt sort ->
  match sort.Ast.sort_desc with
  | Ast.SortProp -> fprintf fmt "Prop"
  | Ast.SortBool -> fprintf fmt "Bool"
  | Ast.SortInt -> fprintf fmt "Int"
  | Ast.SortSymbol string -> fprintf fmt "@[<1>(Symbol %s)@]" string
  | Ast.SortArray s -> fprintf fmt "@[<1>(Array@ %a)@]" pp_sort s
  | Ast.SortDatatype (d, list) ->
    fprintf fmt "@[<1>(Datatype %s@ @[<1>[%a]@])@]"
      d.Ast.dttp_name
      (pp_print_list pp_sort) list
  | Ast.SortDefn (sdef, list) ->
    fprintf fmt "@[<1>(Defn %s@ @[<1>[%a]@])@]"
      sdef.Ast.sdef_name
      (pp_print_list pp_sort) list


let pp_selector fmt slct =
  fprintf fmt "@[<1>{slct %s:@ %a}@]"
    slct.Ast.slct_name
    pp_sort slct.Ast.slct_sort

let pp_constructor fmt cnsr =
  fprintf fmt "@[<1>{cnsr %s:@ @[<1>[%a]@]}@]"
    cnsr.Ast.cnsr_name
    (pp_print_list pp_selector) cnsr.Ast.selectors

let pp_datatype fmt dttp =
  fprintf fmt "@[<1>{dttp %s @[<1>[%a]@]:@ @[<1>[%a]@]}@]"
    dttp.Ast.dttp_name
    (pp_print_list pp_print_string) dttp.Ast.dttp_prms
    (pp_print_list pp_constructor) dttp.Ast.constructors


let pp_var fmt var =
  fprintf fmt "@[<1>{var %s:@ %a}@]"
    var.Ast.var_name
    pp_sort var.Ast.var_sort


let pp_vrop : type a b. formatter -> (a,b) Ast.vrop -> unit =
  fun fmt v ->
  match v with
  | Ast.Distinct -> fprintf fmt "Distinct"

let pp_unop : type a b. formatter -> (a,b) Ast.unop -> unit =
  fun fmt u ->
  match u with
  | Ast.Classic -> fprintf fmt "Classic"
  | Ast.Not -> fprintf fmt "Not"
  | Ast.Succ -> fprintf fmt "Succ"

let pp_bnop  : type a b c. formatter -> (a,b,c) Ast.bnop -> unit =
  fun fmt b ->
  match b with
  | Ast.Imply -> fprintf fmt "Imply"
  | Ast.And   -> fprintf fmt "And"
  | Ast.Or    -> fprintf fmt "Or"
  | Ast.Equal -> fprintf fmt "Equal"
  | Ast.Le    -> fprintf fmt "Le"
  | Ast.Lt    -> fprintf fmt "Lt"
  | Ast.Ge    -> fprintf fmt "Ge"
  | Ast.Gt    -> fprintf fmt "Gt"
  | Ast.Add   -> fprintf fmt "Add"
  | Ast.Sub   -> fprintf fmt "Sub"


let rec pp_term : type a. formatter -> a Ast.term -> unit =
  fun fmt term ->
  match term.Ast.term_desc with
  | Ast.TermTrue -> fprintf fmt "True"
  | Ast.TermFalse -> fprintf fmt "False"
  | Ast.TermBool bool -> fprintf fmt "@[<1>(Bool %b)@]" bool
  | Ast.TermInt int -> fprintf fmt "@[<1>(Int %i)@]" int

  | Ast.TermVar v -> fprintf fmt "@[<1>(Var %a)@]" pp_var v
  | Ast.TermLet (v, b, t) ->
    fprintf fmt "@[<1>(Let %a@ %a@ %a)@]" pp_var v pp_term b pp_term t
  | Ast.TermExists (v, f) ->
    fprintf fmt "@[<1>(Exists %a@ %a)@]" pp_var v pp_term f
  | Ast.TermForall (v, f) ->
    fprintf fmt "@[<1>(Forall %a@ %a)@]" pp_var v pp_term f
  | Ast.TermMatch (t, list) ->
    fprintf fmt "@[<1>(Match@ %a@ @[<1>[%a]@])@]"
      pp_term t (pp_print_list pp_case ) list
  | Ast.TermIte (f, t, e) ->
    fprintf fmt "@[<1>(Ite@ %a@ %a@ %a)@]" pp_term f pp_term t pp_term e

  | Ast.TermVariadic (v, list) ->
    fprintf fmt "@[<1>(%a@ @[<1>[%a]@])@]" pp_vrop v (pp_print_list pp_term) list
  | Ast.TermUnop (u, t) ->
    fprintf fmt "@[<1>(%a@ %a)@]" pp_unop u pp_term t
  | Ast.TermBnop (b, t1, t2) ->
    fprintf fmt "@[<1>(%a@ %a@ %a)@]" pp_bnop b pp_term t1 pp_term t2
  | Ast.TermDecl (fdec, slist, list) ->
    fprintf fmt "@[<1>(Decl %s@ @[<1>[%a]@]@ @[<1>[%a]@])@]"
      fdec.Ast.fdec_name
      (pp_print_list pp_sort) slist
      (pp_print_list pp_term) list
  | Ast.TermDefn (fdef, slist, list) ->
    fprintf fmt "@[<1>(Defn %s@ @[<1>[%a]@]@ @[<1>[%a]@])@]"
      fdef.Ast.fdef_name
      (pp_print_list pp_sort) slist
      (pp_print_list pp_term) list

  | Ast.TermConstruct (d, l, i, list) ->
    fprintf fmt "@[<1>(Construct %i@ %a@ @[<1>[%a]@]@ @[<1>[%a]@])@]"
      i pp_datatype d (pp_print_list pp_sort) l (pp_print_list pp_term) list
  | Ast.TermSelect (d, l, i, j, t) ->
    fprintf fmt "@[<1>(Select %i %i@ %a@ @[<1>[%a]@]@ %a)@]"
      i j pp_datatype d (pp_print_list pp_sort) l pp_term t

  | Ast.ArrayConst (s, e) ->
    fprintf fmt "@[<1>(ArrayConst@ %a@ %a)@]"
      pp_sort s pp_term e
  | Ast.ArrayRead (s, a, i) ->
    fprintf fmt "@[<1>(ArrayRead@ %a@ %a@ %a)@]"
      pp_sort s pp_term a pp_term i
  | Ast.ArrayWrite (s, a, i, e) ->
    fprintf fmt "@[<1>(ArrayWrite@ %a@ %a@ %a@ %a)@]"
      pp_sort s pp_term a pp_term i pp_term e
  | Ast.ArrayMap (fdef, slist, list, a) ->
    fprintf fmt "@[<1>(ArrayMap @[(%s@ @[<1>[%a]@]@ @[<1>[%a]@])@]@ %a)@]"
      fdef.Ast.fdef_name
      (pp_print_list pp_sort) slist
      (pp_print_list pp_term) list
      pp_term a
  | Ast.ArrayDistinct (s, a) ->
    fprintf fmt "@[<1>(ArrayDistinct@ %a@ %a)@]"
      pp_sort s pp_term a


and pp_case : type a. formatter -> a Ast.case -> unit =
  fun  fmt case ->
  fprintf fmt "@[<1>{case %s:@ @[<1>[%a]@]@ %a}@]"
    case.Ast.case_name
    (pp_print_list pp_var) case.Ast.case_vars
    pp_term case.Ast.case_desc

let pp_sortdefn fmt Ast.{ sdef_name; sdef_prms; sdef_desc; _ } =
  fprintf fmt "@[<1>{sdef %s:@ @[<1>[%a]@]@ %a}@]"
    sdef_name
    (pp_print_list pp_print_string) sdef_prms
    pp_sort sdef_desc

let pp_fundecl fmt Ast.{ fdec_name; fdec_prms; fdec_vars; fdec_desc; _ } =
  fprintf fmt "@[<1>{fdec %s:@ @[<1>[%a]@]@ @[<1>[%a]@]@ %a}@]"
    fdec_name
    (pp_print_list pp_print_string) fdec_prms
    (pp_print_list pp_sort) fdec_vars
    pp_sort fdec_desc

let pp_fundefn fmt Ast.{ fdef_name; fdef_prms; fdef_vars; fdef_desc; _ } =
  fprintf fmt "@[<1>{fdef %s:@ @[<1>[%a]@]@ @[<1>[%a]@]@ %a}@]"
    fdef_name
    (pp_print_list pp_print_string) fdef_prms
    (pp_print_list pp_var) fdef_vars
    pp_term fdef_desc

let pp_relation fmt Ast.{ rela_name; rela_prms; _ } =
  fprintf fmt "@[<1>{rela %s:@ @[<1>[%a]@]}@]"
    rela_name
    (pp_print_list pp_sort) rela_prms

let pp_rule fmt Ast.{ rule_name; rule_vars; rule_desc; _ } =
  fprintf fmt "@[<1>{rule %s:@ @[<1>[%a]@]@ %a}@]"
    rule_name
    (pp_print_list pp_var) rule_vars
    pp_term rule_desc

let pp fmt (t: Ast.t) =
  match t with
  | Ast.Datatype dttp ->
    fprintf fmt "Datatype @[<1>%a@]"
      pp_datatype dttp
  | Ast.Sort sort ->
    fprintf fmt "Sort @[<1>%a@]"
      pp_sortdefn sort
  | Ast.Function fdef ->
    fprintf fmt "Function @[<1>%a@]"
      pp_fundefn fdef
  | Ast.Predicate fdef ->
    fprintf fmt "Predicate @[<1>%a@]"
      pp_fundefn fdef
  | Ast.Query rela ->
    fprintf fmt "Query @[<1>%a@]"
      pp_relation rela
  | Ast.Relation rela ->
    fprintf fmt "Relation @[<1>%a@]"
      pp_relation rela
  | Ast.Rule rule ->
    fprintf fmt "Rule @[<1>%a@]"
      pp_rule rule

