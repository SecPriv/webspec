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

type numeral = int

type constant =
  | CstNumeral of int
  | CstString of string
  | CstBool of bool

type symbol = {
  symbol_desc : string;
  symbol_hash : int;
}

type symbols = symbol list

type index =
  | IdxNum of numeral
  | IdxSymbol of symbol

type indexes = index list

type id_desc =
  | IdSymbol of symbol
  | IdUnderscore of symbol * indexes

type identifier = {
  id_desc : id_desc;
  id_hash : int;
}

type sort = {
  sort_desc : sort_desc;
  sort_hash : int;
}

and sorts = sort list

and sort_desc =
  | SortIdentifier of identifier
  | SortFun of identifier * sorts

type qual_identifier_desc =
  | QualIdentifierIdentifier of identifier
  | QualIdentifierAs of identifier * sort

type qual_identifier = {
  qual_identifier_desc : qual_identifier_desc;
  qual_identifier_hash : int;
}

type sorted_var_desc = SortedVar of symbol * sort

type sorted_var = {
  sorted_var_desc : sorted_var_desc;
  sorted_var_hash : int;
}

type sorted_vars = sorted_var list

type pattern_desc = Pattern of symbol * symbols

type pattern = {
  pattern_desc : pattern_desc;
  pattern_hash : int;
}

type term_desc =
  | TermSpecConstant of constant
  | TermQualIdentifier of qual_identifier
  | TermQualIdentifierTerms of qual_identifier * terms
  | TermLetTerm of var_bindings * term
  | TermForallTerm of sorted_vars * term
  | TermExistsTerm of sorted_vars * term
  | TermMatchTerm of term * match_cases

and term = {
  term_desc : term_desc;
  term_hash  : int;
}

and terms = term list

and var_binding_desc = VarBinding of symbol * term

and var_binding = {
  var_binding_desc : var_binding_desc;
  var_binding_hash : int
}

and var_bindings = var_binding list

and match_case_desc = MatchCase of pattern * term

and match_case = {
  match_case_desc : match_case_desc;
  match_case_hash : int;
}

and match_cases = match_case list

type selector_dec_desc = SelectorDec of symbol * sort

type selector_dec = {
  selector_dec_desc : selector_dec_desc;
  selector_dec_hash : int;
}

type selector_decs = selector_dec list

type constructor_dec_desc = ConstructorDec of symbol * selector_decs

type constructor_dec = {
  constructor_dec_desc : constructor_dec_desc;
  constructor_dec_hash : int;
}

type constructor_decs = constructor_dec list

type datatype_dec_desc = DatatypeDec of symbols * constructor_decs

type datatype_dec = {
  datatype_dec_desc : datatype_dec_desc;
  datatype_dec_hash : int;
}

type command_desc =
  | CmdAssert of term
  | CmdCheckSat
  | CmdComment of string
  | CmdDeclareFun of symbol * sorts option * sorts * sort
  | CmdDeclareDatatype of symbol * datatype_dec
  | CmdDeclareRel of symbol * sorts
  | CmdDeclareSort of symbol * numeral
  | CmdDeclareVar of symbol * sort
  | CmdDefineFun of symbol * sorts option * sorted_vars * sort * term
  | CmdDefineSort of symbol * symbols * sort
  | CmdEcho of string
  | CmdExit
  | CmdGetModel
  | CmdGetValue of terms
  | CmdQuery of symbol
  | CmdRule of term * symbol option
  | CmdSetLogic of symbol

type command = {
  command_desc : command_desc;
  command_hash : int;
}

type commands = command list

type script = {
  script_commands : commands;
  script_hash     : int;
}


(******************************************************************************)


let mk_symbol (s:string) =
  { symbol_desc = s; symbol_hash = 0 }

let mk_idx_num i    = IdxNum i
let mk_idx_symbol s = IdxSymbol s


let mk_identifier id_desc =
  { id_desc; id_hash = 0 }

let mk_id_symbol symbol =
  mk_identifier (IdSymbol symbol)

let mk_id_underscore symbol indexes =
  mk_identifier (IdUnderscore (symbol,indexes))


let mk_sort sort_desc =
  { sort_desc; sort_hash = 0 }

let mk_sort_identifier identifier =
  mk_sort (SortIdentifier identifier)

let mk_sort_fun identifier sorts =
  mk_sort (SortFun (identifier, sorts))


let mk_qual_identifier qual_identifier_desc =
  { qual_identifier_desc; qual_identifier_hash = 0 }

let mk_qual_identifier_identifier identifier =
  mk_qual_identifier (QualIdentifierIdentifier identifier)

let mk_qual_identifier_as identifier sort =
  mk_qual_identifier (QualIdentifierAs (identifier, sort))


let mk_sorted_var symbol sort =
  let sorted_var_desc = SortedVar (symbol, sort) in
  let sorted_var_hash = 0 in
  { sorted_var_desc; sorted_var_hash }

let mk_var_binding symbol term =
  let var_binding_desc = VarBinding (symbol, term) in
  let var_binding_hash = 0 in
  { var_binding_desc; var_binding_hash }


let mk_pattern symbol symbols =
  let pattern_desc = Pattern (symbol, symbols) in
  let pattern_hash = 0 in
  { pattern_desc; pattern_hash }

let mk_match_case pattern term =
  let match_case_desc = MatchCase (pattern, term) in
  let match_case_hash = 0 in
  { match_case_desc; match_case_hash }


let mk_term term_desc =
  { term_desc; term_hash = 0 }

let mk_term_spec_constant constant =
  mk_term (TermSpecConstant constant)

let mk_term_qual_identifier qual_identifier =
  mk_term (TermQualIdentifier qual_identifier)

let mk_term_qual_identifier_terms qual_identifier terms =
  mk_term (TermQualIdentifierTerms (qual_identifier, terms))

let mk_term_let_term var_bindings term =
  mk_term (TermLetTerm (var_bindings, term))

let mk_term_forall_term sorted_vars term =
  mk_term (TermForallTerm (sorted_vars, term))

let mk_term_exists_term sorted_vars term =
  mk_term (TermExistsTerm (sorted_vars, term))

let mk_term_match_term term match_cases =
  mk_term (TermMatchTerm (term, match_cases))


let mk_selector_dec symb sort =
  let selector_dec_desc = SelectorDec (symb, sort) in
  { selector_dec_desc; selector_dec_hash = 0 }

let mk_constructor_dec symb slct_decs =
  let constructor_dec_desc = ConstructorDec (symb, slct_decs) in
  { constructor_dec_desc; constructor_dec_hash = 0 }

let mk_datatype_dec symbs cnst_decs =
  let datatype_dec_desc = DatatypeDec (symbs, cnst_decs) in
  { datatype_dec_desc; datatype_dec_hash = 0 }


let mk_command (cmd : command_desc) : command =
  { command_desc = cmd; command_hash = 0; }

let mk_cmd_assert term =
  mk_command (CmdAssert term)

let mk_cmd_check_sat =
  mk_command (CmdCheckSat)

let mk_cmd_declare_fun symbol sorts sort =
  mk_command (CmdDeclareFun (symbol, None, sorts, sort))

let mk_cmd_declare_datatype symbol dttp_dec =
  mk_command (CmdDeclareDatatype (symbol, dttp_dec))

let mk_cmd_declare_rel symbol sorts =
  mk_command (CmdDeclareRel (symbol, sorts))

let mk_cmd_declare_sort symbol numeral =
  mk_command (CmdDeclareSort (symbol, numeral))

let mk_cmd_declare_var symbol sort =
  mk_command (CmdDeclareVar (symbol, sort))

let mk_cmd_define_fun symbol sorted_vars sort term =
  mk_command (CmdDefineFun (symbol, None, sorted_vars, sort, term))

let mk_cmd_define_sort symbol symbols sort =
  mk_command (CmdDefineSort (symbol, symbols, sort))

let mk_cmd_echo string =
  mk_command (CmdEcho string)

let mk_cmd_query symbol =
  mk_command (CmdQuery symbol)

let mk_cmd_rule term opt =
  mk_command (CmdRule (term, opt))

