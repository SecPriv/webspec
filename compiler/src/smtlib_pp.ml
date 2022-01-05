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
open Smtlib

let pp_list pp_f ppf elts =
  let rec pp_list_aux ppf = function
    | [] -> ()
    | [e] -> fprintf ppf "%a" pp_f e
    | e :: es -> fprintf ppf "%a@ %a" pp_f e pp_list_aux es
  in pp_list_aux ppf elts

let pp_numeral ppf n = fprintf ppf "%i" n

let pp_symbol ppf symb =
  fprintf ppf "%s" symb.symbol_desc

let pp_symbols ppf symbs = fprintf ppf "%a" (pp_list pp_symbol) symbs

let pp_spec_constant ppf = function
  | CstBool b -> fprintf ppf "%b" b
  | CstNumeral n -> pp_numeral ppf n
  | CstString str -> fprintf ppf "\"%s\"" str

let pp_idx ppf idx =
  match idx with
  | IdxNum n -> pp_numeral ppf n
  | IdxSymbol symb -> pp_symbol ppf symb

let pp_indexes ppf indexes = pp_list pp_idx ppf indexes

let pp_identifier ppf identifier =
  match identifier.id_desc with
  | IdSymbol symb -> pp_symbol ppf symb
  | IdUnderscore (symb, indexes) ->
    fprintf ppf "@[<hov 1>(_@ %a@ %a)@]"
      pp_symbol symb
      pp_indexes indexes

let rec pp_sort ppf sort =
  match sort.sort_desc with
  | SortIdentifier id -> pp_identifier ppf id
  | SortFun (id, sorts) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]"
      pp_identifier id pp_sorts sorts

and pp_sorts ppf sorts = pp_list pp_sort ppf sorts

let pp_qual_identifier ppf qualid =
  match qualid.qual_identifier_desc with
  | QualIdentifierIdentifier id ->
    fprintf ppf "%a" pp_identifier id
  | QualIdentifierAs (id, sort) ->
    fprintf ppf "@[<hov 1>(as@ %a@ %a)@]"
      pp_identifier id
      pp_sort sort

let pp_sorted_var ppf svar =
  match svar.sorted_var_desc with
  | SortedVar (symb, sort) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]" pp_symbol symb pp_sort sort

let pp_sorted_vars ppf svars = fprintf ppf "%a" (pp_list pp_sorted_var) svars

let pp_pattern ppf pattern =
  match pattern.pattern_desc with
  | Pattern (symb, []) -> pp_symbol ppf symb
  | Pattern (symb, symbs) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]" pp_symbol symb pp_symbols symbs

let rec pp_term ppf term =
  match term.term_desc with
  | TermSpecConstant sc -> pp_spec_constant ppf sc
  | TermQualIdentifier qualid -> pp_qual_identifier ppf qualid
  | TermQualIdentifierTerms (qualid, terms) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]"
      pp_qual_identifier qualid
      pp_terms terms
  | TermLetTerm (varbindings, term) ->
    fprintf ppf "@[<hov 1>(let@ (@[<hov 0>%a@])@ %a)@]"
      pp_var_bindings varbindings
      pp_term term
  | TermForallTerm (svars, term) ->
    fprintf ppf "@[<hov 1>(forall@ (@[<hov 0>%a@])@ %a)@]"
      pp_sorted_vars svars
      pp_term term
  | TermExistsTerm (svars, term) ->
    fprintf ppf "@[<hov 1>(exists@ (@[<hov 0>%a@])@ %a)@]"
      pp_sorted_vars svars
      pp_term term
  | TermMatchTerm (term, mcases) ->
    fprintf ppf "@[<hov 1>(match@ %a@ (@[<hov 0>%a@]))@]"
      pp_term term
      pp_match_cases mcases

and pp_terms ppf terms = fprintf ppf "%a" (pp_list pp_term) terms

and pp_var_binding ppf vbinding =
  match vbinding.var_binding_desc with
  | VarBinding (symb, term) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]" pp_symbol symb pp_term term

and pp_var_bindings ppf vbindings = pp_list pp_var_binding ppf vbindings

and pp_match_case ppf mcase =
  match mcase.match_case_desc with
  | MatchCase (pattern, term) ->
    fprintf ppf "@[<hov 1>(%a@ %a)@]" pp_pattern pattern pp_term term

and pp_match_cases ppf mcases = fprintf ppf "%a" (pp_list pp_match_case) mcases

let pp_selector_dec ppf slct_dec =
  match slct_dec.selector_dec_desc with
  | SelectorDec (symb, sort) ->
    fprintf ppf "@[<hov 1>(%a %a)@]"
      pp_symbol symb
      pp_sort sort

let pp_selector_decs ppf slct_decs =
  fprintf ppf "%a" (pp_list pp_selector_dec) slct_decs

let pp_constructor_dec ppf cnst_dec =
  match cnst_dec.constructor_dec_desc with
  | ConstructorDec (symb, slct_decs) ->
    fprintf ppf "@[<hov 1>(%a@ @[<hov 0>%a@])@]"
      pp_symbol symb
      pp_selector_decs slct_decs

let pp_constructor_decs ppf cnst_decs =
  fprintf ppf "%a" (pp_list pp_constructor_dec) cnst_decs

let pp_datatype_dec ppf dttp_dec =
  match dttp_dec.datatype_dec_desc with
  | DatatypeDec (symbs, cnst_decs) ->
    match symbs with
    | [] ->
      fprintf ppf "@[<hov 1>(%a)@]"
        pp_constructor_decs cnst_decs
    | _ ->
      fprintf ppf "@[<hov 1>(par@ (@[<hov 0>%a@])@ (@[<hov 0>%a@]))@]"
        pp_symbols symbs
        pp_constructor_decs cnst_decs

let pp_opt_type_parameters ppf optsorts =
  match optsorts with
  | Some sorts -> fprintf ppf "par@ (@[<hov 1>%a@])@ " pp_sorts sorts
  | None -> ()

let pp_command ppf cmd =
  match cmd.command_desc with

  | CmdAssert t -> fprintf ppf "(assert@ %a)" pp_term t

  | CmdCheckSat -> fprintf ppf "(check-sat)"

  | CmdComment str -> fprintf ppf ";; %s@\n" str

  | CmdDeclareFun (symb, _, sorts, sort) ->
    fprintf ppf "(declare-fun %a@ (%a)@ %a)"
      pp_symbol symb
      pp_sorts sorts
      pp_sort sort

  | CmdDeclareDatatype (symbol, dttp_dec) ->
    fprintf ppf "(declare-datatype %a@ %a)"
      pp_symbol symbol
      pp_datatype_dec dttp_dec

  | CmdDeclareRel (symb, sorts) ->
    fprintf ppf "(declare-rel %a@ (%a))"
      pp_symbol symb
      pp_sorts sorts

  | CmdDeclareSort (symb, num) ->
    fprintf ppf "(declare-sort %a@ %a)"
      pp_symbol symb
      pp_numeral num

  | CmdDeclareVar (symb, sort) ->
    fprintf ppf "(declare-var %a@ %a)"
      pp_symbol symb
      pp_sort sort

  | CmdDefineFun (symb, optsorts , svars, sort, term) ->
    fprintf ppf "(define-fun %a@ %a@[<hov 0>(%a)@]@ %a@ @[<hov 1>%a@])"
      pp_symbol symb
      pp_opt_type_parameters optsorts
      pp_sorted_vars svars
      pp_sort sort pp_term term

  | CmdDefineSort (symb, symbs, sort) ->
    fprintf ppf "(define-sort %a@ (%a)@ %a)"
      pp_symbol symb
      pp_symbols symbs
      pp_sort sort

  | CmdExit -> fprintf ppf "(exit)"

  | CmdEcho s -> fprintf ppf "(echo@ \"%s\")" s

  | CmdGetModel-> fprintf ppf "(get-model)"

  | CmdGetValue terms -> fprintf ppf "(get-value@ (%a))" pp_terms terms

  | CmdQuery symb -> fprintf ppf "(query@ %a)" pp_symbol symb

  | CmdRule (term, None) -> fprintf ppf "(rule@ %a)" pp_term term

  | CmdRule (term, Some symb) -> fprintf ppf "(rule@ %a@ %a)" pp_term term pp_symbol symb

  | CmdSetLogic symb -> fprintf ppf "(set-logic@ %a)" pp_symbol symb

let pp_command ppf cmd =
  fprintf ppf "@[<hov 1>%a@]@\n@." pp_command cmd

let pp_commands ppf cmds =
  List.iter (fun cmd -> Format.fprintf ppf "%a" pp_command cmd) cmds

let pp ppf (s: script) =
  pp_commands ppf s.script_commands

let pp_tofile filename program =
  let oc = Stdlib.open_out_bin filename in
  let ppf = Format.formatter_of_out_channel oc in
  Format.fprintf ppf "%a@." pp program;
  close_out oc
