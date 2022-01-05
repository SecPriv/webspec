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


val mk_symbol : string -> symbol

val mk_idx_num    : int -> index
val mk_idx_symbol : symbol -> index

val mk_id_symbol     : symbol -> identifier
val mk_id_underscore : symbol -> indexes -> identifier

val mk_sort_identifier : identifier -> sort
val mk_sort_fun : identifier -> sorts -> sort

val mk_qual_identifier_identifier : identifier -> qual_identifier
val mk_qual_identifier_as : identifier -> sort -> qual_identifier

val mk_sorted_var  : symbol -> sort -> sorted_var
val mk_var_binding : symbol -> term -> var_binding

val mk_pattern    : symbol -> symbols -> pattern
val mk_match_case : pattern -> term -> match_case

val mk_term_spec_constant         : constant -> term
val mk_term_qual_identifier       : qual_identifier -> term
val mk_term_qual_identifier_terms : qual_identifier -> terms -> term
val mk_term_let_term              : var_bindings -> term -> term
val mk_term_forall_term           : sorted_vars -> term -> term
val mk_term_exists_term           : sorted_vars -> term -> term
val mk_term_match_term            : term -> match_cases -> term

val mk_selector_dec    : symbol -> sort -> selector_dec
val mk_constructor_dec : symbol -> selector_decs -> constructor_dec
val mk_datatype_dec    : symbols -> constructor_decs -> datatype_dec

val mk_cmd_assert           : term -> command
val mk_cmd_check_sat        : command
val mk_cmd_declare_fun      : symbol -> sorts -> sort -> command
val mk_cmd_declare_datatype : symbol -> datatype_dec -> command
val mk_cmd_declare_rel      : symbol -> sorts -> command
val mk_cmd_declare_sort     : symbol -> numeral -> command
val mk_cmd_declare_var      : symbol -> sort -> command
val mk_cmd_define_fun       : symbol -> sorted_vars -> sort -> term -> command
val mk_cmd_define_sort      : symbol -> symbols -> sort -> command
val mk_cmd_echo             : string -> command
val mk_cmd_query            : symbol -> command
val mk_cmd_rule             : term -> symbol option -> command

