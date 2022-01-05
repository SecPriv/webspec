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

Definition array (T : Type) := nat -> T.
Definition const (T : Type) (e : T) : array T := fun (i : nat) => e.

Definition select (T : Type) (a : array T) (i : nat) : T := a i.
Definition store  (T : Type) (a : array T) (i : nat) (e : T) : array T :=
  fun j => if Nat.eqb i j then e else a j.

Definition map {T U : Type} (f : T -> U) (a : array T) : array U :=
  fun (i : nat) => f (select _ a i).

Definition pairwise {T : Type} (P : T -> T -> Prop) (a : array T) : Prop :=
  forall (i j : nat), i <> j -> P (select _ a i) (select _ a j).

Definition distinct {T : Type} (a : array T) : Prop := pairwise (fun x y => x <> y) a.

Notation "[| E |]" := (const _ E) (at level 80, format "[| E |]").
Notation "A .[ I ]" := (select _ A I) (at level 80, format "A .[ I ]").
Notation "A .[ I ] <- E" := (store _ A I E) (at level 80, format "A .[ I ] <- E").
