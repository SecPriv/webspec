(********************************************************************************)
(*  Copyright (c) 2022 Pedro Bernardo & Lorenzo Veronese                        *)
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

(* Args *)
let verbose = ref false
let lemma = ref None
let check = ref None
let trace = ref None
let trace_name = ref None

let usage = Printf.sprintf "%s [-v] [-l <lemma.dat>] [-c <csp|...>] <trace.dat>" Sys.argv.(0)
let speclist =
  [("-v", Arg.Set verbose, "Print debug info");
   ("-l", Arg.String (fun s -> lemma := Some (Trace.get_trace s)), "Load (and merge) the lemma trace") ;
   ("-c", Arg.String (fun s -> check := Some (s)), "Perform additional check at the end of the trace")]


let anon_fun filename =
  if Option.is_some !trace then
    raise (Arg.Bad "only one trace expected");
  trace := Some (Trace.get_trace filename);
  trace_name := Some Filename.(filename |> remove_extension |> basename)

let () =
  Arg.parse speclist anon_fun usage;
  if Option.is_some !lemma then
    trace := Some (Trace.merge_traces (Option.get !lemma) (Option.get !trace));
  let trace = (Option.get !trace) in

  (* make the output directory if it does not exists *)
  if not (Sys.file_exists "output") then
    Unix.mkdir "output" 0o755;

  let pairs = Utils.event_state_pairs (List.rev trace.events) trace.states in 

  let st = States.VerifierState.empty in
  let st = { st with trace=Some(trace) } in 

  let st = List.fold_left Visitor.Preprocessor.handle st pairs in

  (* HERE, PASS FOR THE CSP CHECKS *)
  let st = if Option.is_some !check then (Cspcheck.CSPChecker.generate_checks st ) else ( st ) in
  let st = Script.Script.generate_scripts st in
  let st = List.fold_left Visitor.ResponseGenerator.handle st pairs in

  let all_asserts = List.concat [st.asserts ; st.asserts_ordered] in 

  let asserts : Jingoo.Jg_types.tvalue list = 
    List.fold_left (fun acc (e : States.assertion_t) -> (
      (Jingoo.Jg_types.Tobj [ ("uuid", Jingoo.Jg_types.Tstr e.uuid) ;
                    ("value", Jingoo.Jg_types.Tstr e.value) ; 
                    ("tag", Jingoo.Jg_types.Tstr (Printf.sprintf "test %d" (List.length acc)))
                  ]) :: acc 
    )) [] all_asserts
  in

  let actions : Jingoo.Jg_types.tvalue list = 
    List.fold_left (fun acc (e : States.action_t) -> (
      let ass = List.nth st.asserts_ordered e.assertion in
      acc @ [(Jingoo.Jg_types.Tobj [ 
        ("repr", Jingoo.Jg_types.Tstr e.repr)  ;
        ("wait", Jingoo.Jg_types.Tbool (
          let w = States.VerifierState.get_wait_uuid st ass in
          match w with | Some(_) -> true | None -> false
        ) ) ;
        ("trigger", Jingoo.Jg_types.Tbool (
          let w = States.VerifierState.get_next_uuid st ass in
          match w with | Some(_) -> true | None -> false
        ) ) ;
        ("lock", Jingoo.Jg_types.Tstr (ass.lock)) ;
        ("uuid", Jingoo.Jg_types.Tstr (ass.uuid)) ;
        ("value",Jingoo.Jg_types.Tstr (ass.value)) ;
        ("next", Jingoo.Jg_types.Tstr (
          let w = States.VerifierState.get_next_uuid st ass in
          match w with | Some(x) -> x | None -> ""
          )) ; 
      ])]
    )) [] st.actions
  in
  
  let setup = List.fold_left
    (fun acc x -> acc @ [Jingoo.Jg_types.Tstr (Script.Script.generate_sw st x)])
    [] st.sws
  in

  let result = Jingoo.Jg_template.from_file "templates/launcher.jingoo" ~models:[
    ("delay", Jingoo.Jg_types.Tint 10000) ;
    ("actions", Jingoo.Jg_types.Tlist actions) ;
    ("asserts", Jingoo.Jg_types.Tlist asserts) ;
    ("sws", Jingoo.Jg_types.Tlist setup) ;
    ("name", Jingoo.Jg_types.Tstr (Option.get !trace_name)) ;
  ] in

  Utils.write_to_file "output/launcher.html" result ;

  let conf = Yojson.Safe.pretty_to_string (Wpt.Config.to_yojson (Wpt.Config.state_to_config st)) in
  Utils.write_to_file "output/config.json" conf 
