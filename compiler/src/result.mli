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


type 'a t = ('a, exn) result


module Monad :
sig

  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t

  val (>>|) : 'a t -> ('a -> 'b) -> 'b t

  val return : 'a t -> 'a

  val failure : ((('a, unit, string) format -> 'a) -> string) -> 'b t

end


module Option :
sig

  val map : ('a -> 'b t) -> 'a option -> 'b option t

end


module Array :
sig

  val fold_left : ('a -> 'b -> 'a t) -> 'a t -> 'b array -> 'a t

  val fold_right : ('b -> 'a -> 'a t) -> 'b array -> 'a t -> 'a t

  val map  : ('a -> 'b t) -> 'a array -> 'b array t

  val map2 : ('a -> 'b -> 'c t) -> 'a array -> 'b array -> 'c array t

end


module List :
sig

  val fold_left : ('a -> 'b -> 'a t) -> 'a t -> 'b list -> 'a t

  val fold_right : ('b -> 'a -> 'a t) -> 'b list -> 'a t -> 'a t

  val map  : ('a -> 'b t) -> 'a list -> 'b list t

  val map2 : ('a -> 'b -> 'c t) -> 'a list -> 'b list -> 'c list t

  val filter_map : ('a -> 'b option t) -> 'a list -> 'b list t

end

