(*#use "topfind";;*)
#require "sexplib";;
#install_printer Sexplib.Sexp.pp_hum;;
#use "scripts/viz.ml"

open Sexplib
open Printf

type environment = (string * Sexp.t) list

let rec find_final_state (form : Sexp.t) =
  let rec cons_env env new_binds : environment =
    List.append
      (List.map (function
           | (Sexp.List [Sexp.Atom name; valu]) -> (name, expand_sexp env valu)
           | _ -> failwith "invalid let binding") new_binds)
      env
  and expand_sexp env sexp : Sexp.t = match sexp with
    | Sexp.Atom name -> Option.value
                          (Option.map snd (List.find_opt (fun (vname, _) -> name = vname) env))
                          ~default:(Sexp.Atom name)
    | Sexp.List xs -> Sexp.List (List.map (fun x -> expand_sexp env x) xs)
  in
  (* Get the query!0 in the last hyper-ref clause and save hypotheses
     (NOTE: the query!0 depends on the format of the query) *)
  let rec go (env : environment) hyp form =
    let open Sexp in
    match form with
    | List [Atom "let"; List binds; body] -> go (cons_env env binds) hyp body
    | List [Atom "hyper-res"; fst; snd; body] -> go env (hyp @ get_hyp env fst @ get_hyp env snd) (expand_sexp env body)
    | List [Atom query; final_state; lst; global] when String.sub query 0 6 = "query!" -> Some (expand_sexp env final_state, expand_sexp env global, hyp, lst)
    | _ -> None
  and get_hyp env sexp =
    let open Sexp in
    match sexp with
    | Atom name -> get_hyp env (expand_sexp env sexp)
    | List (Atom "asserted" :: _) -> [] (* ignore asserted *)
    | List [Atom "hyper-res"; fst; snd; body] -> get_hyp env fst @ get_hyp env snd @ get_hyp env body
    | List [Atom "=>"; hyp'; body] -> [expand_sexp env hyp'] @ get_hyp env body
    | x -> []
  in go [] [] form


let _ =
  let answer =  Sexp.load_sexp Sys.argv.(1) in
  let [@warning "-8"] Some (final_state, global, hyps, lst) = find_final_state answer in
  let states =
    List.filter_map (function | (Sexp.List [Sexp.Atom name; _; _; state])
                                 when name = "Reachable" || name = "reachable" ->  Some state
                              | _ -> None) hyps in
  let [@warning "-8"] sorted_states =
    List.sort (fun (Sexp.List (Sexp.Atom "Build_State" :: Sexp.Atom n :: _))
                   (Sexp.List (Sexp.Atom "Build_State" :: Sexp.Atom n' :: _)) ->
        compare (int_of_string n) (int_of_string n')) states
  in
  printf "%s\n\n%s\n\n%s\n\n%s\n\n"
    (String.concat "\n\n" (List.map Sexp.to_string_hum sorted_states))
    (Sexp.to_string_hum final_state)
    (Sexp.to_string_hum lst)
    (Sexp.to_string_hum global);

  let stlist = sorted_states @ [final_state] in
  let rec cons_to_list = function
  | Sexp.Atom n when String.sub n 0 3 = "nil" -> []
  | Sexp.List [Sexp.Atom n; elm; rest] when String.sub n 0 4 = "cons" -> elm :: (cons_to_list rest)
  | _ -> failwith "invalid cons"
  in
  let rec take n lst = match (n, lst) with
  | n, _ when n<= 0 -> []
  | _, [] -> []
  | _, (x :: xs) -> (x :: take (n-1) xs)
  in
  let evlist = take (List.length stlist) ((cons_to_list lst) @ [Sexp.Atom "EvInit"]) |> List.rev in
  let vizstates = List.map2 (fun st ev ->
    match st with
    | Sexp.List (Sexp.Atom "Build_State" :: version :: rest ) ->
      Sexp.List (Sexp.Atom "Build_State" :: version :: ev :: rest )
    | _ -> st
    ) stlist evlist in
  fprintf stderr "\n\n%s" (Viz.viz vizstates)
