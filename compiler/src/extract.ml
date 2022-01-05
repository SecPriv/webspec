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

open Result.Monad

module Log = Logger.Default
    (struct
      let name = "ast"
    end)

(******************************************************************************)

let used_lemmas = ref []

let use_lemma def =
  let cn =
    return
      (Ok def
       >>= Cic.extract
       >>= Omega.extract_lemma
       >>= Omicron.extract_constant)
  in
  used_lemmas := cn :: !used_lemmas

let inline_constant qualid =
  match Constrintern.locate_reference qualid with
  | Names.GlobRef.ConstRef cn ->
    Config.InlinedConstants.add (Names.Constant.canonical cn)
  | _ -> ()

let inline_relation depth qualid =
  match Constrintern.locate_reference qualid with
  | Names.GlobRef.IndRef (iv, _) ->
    let string = Names.(Label.to_string (MutInd.label iv)) in
    Config.InlinedRelations.add string
      (Stdlib.Option.value depth ~default:(Config.InlineDepth.get ()))
  | _ -> ()

let destruct_relation depth qualid =
  match Constrintern.locate_reference qualid with
  | Names.GlobRef.IndRef (iv, _) ->
    let string = Names.(Label.to_string (MutInd.label iv)) in
    Config.DestructRelations.add string (Stdlib.Option.value depth ~default:max_int)
  | _ -> ()

(******************************************************************************)

let log name t =
  Log.debug (fun fmt -> fmt "%s" name);
  [t]

let log_verbose name t =
  Log.Verbose.debug
    ~head:(fun fmt -> fmt "%s" name)
    ~body:(fun fmt -> fmt "%a" Ast_pp.pp t);
  [t]

let (>|=) list (f: 'a -> 'b list) = List.flatten (List.map f list)

let optimize t =
  log_verbose (Ast_utils.get_name t) t

  >|= log "destruct_rule"
  >|= Ast_transformation.destruct_rule (Config.DestructRelations.bindings ())
  >|= log "inline_relations"
  >|= Ast_transformation.inline_relations (Config.InlinedRelations.bindings ())
(*
    >|= pp_if "destruct_match"
    >|= Ast_transformation.destruct_match
    >|= pp_if "split_rule"
    >|= Ast_transformation.split_rule
    >|= pp_if "unify_equality"
    >|= Ast_transformation.unify_equality
*)
  >|= log "destruct_array"
  >|= Ast_transformation.destruct_array
  >|= log "rename_vars"
  >|= Ast_transformation.rename_vars
  >|= log_verbose (Ast_utils.get_name t)

(******************************************************************************)

module type S =
sig
  type t
  val extract : Constrexpr.constr_expr -> t list
end

module Horn =
struct

  type t = Smtlib.command

  let extract def =
    return
      (Ok def
       >>= Cic.extract
       >>= Omega.extract_relation
       >>= Omicron.extract_inductive
       >>= Temporary.extract_inductive ~lemmas:!used_lemmas)
    >|= optimize
    >|= Smtlib_utils.ast_to_horn

end

module Smtlib =
struct

  type t = Smtlib.command

  let extract def =
    return
      (Ok def
       >>= Cic.extract
       >>= Omega.extract_relation
       >>= Omicron.extract_inductive
       >>= Temporary.extract_inductive ~lemmas:!used_lemmas)
    >|= optimize
    >|= Smtlib_utils.ast_to_smtlib

end
