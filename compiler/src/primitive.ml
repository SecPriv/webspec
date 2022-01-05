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

type relation =
  | True
  | False
  | Eq
  | Lt
  | Le
  | Gt
  | Ge
  | And
  | Or
  | Not
  | ArrayDistinct

let relation_to_string = function
  | True -> "True"
  | False-> "False"
  | Eq   -> "eq"
  | Lt   -> "lt"
  | Le   -> "le"
  | Gt   -> "gt"
  | Ge   -> "ge"
  | And  -> "and"
  | Or   -> "or"
  | Not  -> "not"
  | ArrayDistinct-> "array_distinct"

let string_to_relation = function
  | "True" -> Some True
  | "False"-> Some False
  | "eq"   -> Some Eq
  | "lt"   -> Some Lt
  | "le"   -> Some Le
  | "gt"   -> Some Gt
  | "ge"   -> Some Ge
  | "and"  -> Some And
  | "or"   -> Some Or
  | "not"  -> Some Not
  | _      -> None


type constant =
  | IntAdd
  | IntSub
  | IntMul
  | IntDiv
  | IntMod
  | IntEq
  | IntLt
  | IntLe
  | FloatAdd
  | FloatSub
  | FloatMul
  | FloatDiv
  | FloatAbs
  | FloatSqrt
  | FloatEq
  | FloatLt
  | FloatLe
  | ArrayMake
  | ArrayDefault
  | ArrayGet
  | ArraySet
  | ArrayCopy
  | ArrayLength
  | ArrayMap
  | Eqb

let constant_to_string = function
  | IntAdd       -> "int_add"
  | IntSub       -> "int_sub"
  | IntMul       -> "int_mul"
  | IntDiv       -> "int_div"
  | IntMod       -> "int_mod"
  | IntEq        -> "int_eq"
  | IntLt        -> "int_lt"
  | IntLe        -> "int_le"
  | FloatAdd     -> "float_add"
  | FloatSub     -> "float_sub"
  | FloatMul     -> "float_mul"
  | FloatDiv     -> "float_div"
  | FloatAbs     -> "float_abs"
  | FloatSqrt    -> "float_sqrt"
  | FloatEq      -> "float_eq"
  | FloatLt      -> "float_lt"
  | FloatLe      -> "float_le"
  | ArrayMake    -> "array_make"
  | ArrayDefault -> "array_default"
  | ArrayGet     -> "array_get"
  | ArraySet     -> "array_set"
  | ArrayCopy    -> "array_copy"
  | ArrayLength  -> "array_length"
  | ArrayMap     -> "array_map"
  | Eqb          -> "eqb"


type t = Relation of relation | Constant of constant

let to_string = function
  | Relation rela -> relation_to_string rela
  | Constant cnst -> constant_to_string cnst
