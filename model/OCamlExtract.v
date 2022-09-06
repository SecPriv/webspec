Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.

Require Import Browser.

Require Extraction.
Extraction Language OCaml.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".
Extract Constant Nat.eqb => "( = )".

Extract Constant Array.array "'a" => "(int * 'a) list [@@deriving yojson, show, eq, ord]".
Extract Constant Array.const => "(fun x -> [(-1, x)])".
Extract Constant Array.store => "(fun a i x -> (i,x) :: a)".
Extract Constant Array.select => "(fun a i -> Option.value (List.assoc_opt i a) ~default:(List.assoc (-1) a))".
Extract Constant Array.map => "(fun f a -> List.map (fun (i, x) -> (i, f x)) a)".

Cd "../verifier/model/".
Separate Extraction Array State Global Event.
