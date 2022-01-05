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

(** Pretty-printer for SMT-LIB AST *)
val pp_spec_constant : Format.formatter -> Smtlib.constant -> unit

val pp_symbol : Format.formatter -> Smtlib.symbol -> unit
(** pretty-prints a SMT symbol *)

val pp_sort : Format.formatter -> Smtlib.sort -> unit
(** pretty-prints a SMT sort *)

val pp_term : Format.formatter -> Smtlib.term -> unit
(** pretty-prints a SMT term *)

val pp_qual_identifier : Format.formatter -> Smtlib.qual_identifier -> unit
(** pretty-prints a SMT qualified identifier *)

val pp: Format.formatter -> Smtlib.script -> unit
(** [pp fmt ast] pretty-prints a full SMT-LIB script onto a formatter *)

val pp_command: Format.formatter -> Smtlib.command -> unit

val pp_commands: Format.formatter -> Smtlib.commands -> unit
(** pp_commands pretty_prints an arbitrary command list onto a formatter.
    Used by pp.
*)

val pp_tofile: string -> Smtlib.script -> unit
(** [pp_tofile filename script] Prints a SMT-LIB script into the file named
 ** [filename]. The file is created if needed. Contents from any present file is
 ** not preserved.
*)
