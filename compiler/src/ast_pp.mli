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

val pp_sort : Format.formatter -> _ Ast.sort -> unit

val pp_selector : Format.formatter -> Ast.selector -> unit

val pp_constructor : Format.formatter -> Ast.constructor -> unit

val pp_datatype : Format.formatter -> Ast.datatype -> unit

val pp_var : Format.formatter -> Ast.var -> unit

val pp_case : Format.formatter -> _ Ast.case -> unit

val pp_term : Format.formatter -> _ Ast.term -> unit

val pp_sortdefn : Format.formatter -> Ast.sortdefn -> unit

val pp_fundecl : Format.formatter -> _ Ast.fundecl -> unit

val pp_fundefn : Format.formatter -> _ Ast.fundefn -> unit

val pp_rule : Format.formatter -> Ast.rule -> unit

val pp_relation : Format.formatter -> Ast.relation -> unit

val pp : Format.formatter -> Ast.t -> unit
