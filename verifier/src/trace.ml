(********************************************************************************)
(*  Copyright (c) 2021 Lorenzo Veronese                                          *)
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

open Model
open Model.Browser

type t = {
  events : Browser.coq_Event list;
  states : Browser.coq_State list;
  global : Browser.coq_Global;
}

let get_trace filename : t =
  let channel = open_in_bin filename in
  Fun.protect (fun () -> Marshal.from_channel channel)
    ~finally: (fun () -> close_in channel)


module IndexWindowSet =
  Set.Make (struct
      type t = (int * Types.Window.t)
      let compare (a, wa) (b, wb) =
        match Stdlib.compare a b with
        | 0 -> Types.Window.compare wa wb
        | c -> c
    end)

module UpdateBrowser = struct
  let update_st_window st f = { st with st_window = f st.st_window }
  let update_wd_document wd f = { wd with wd_document = f wd.wd_document }
  let update_dc_dom dc f = { dc with dc_dom = f dc.dc_dom }
  let update_dm_body dm f = { dm with dm_body = f dm.dm_body }
end

let rec get_referred_windows wd gb =
  let open IndexWindowSet in
  let equal_windows = List.find_all (fun (_, wd') -> Types.Window.equal wd wd') gb.windows in
    List.fold_left (fun acc (_, oelm) ->
        Option.map (fun elm ->
            match elm with
            | DOMElementResource (_, ContentElementFrame (frame, _)) ->
               let inner = Array.select gb.windows frame.frame_window in
               let refs = get_referred_windows inner gb in
               add (frame.frame_window, inner) @@ union acc refs
            | _ -> acc) oelm
        |> Option.value ~default:acc)
      (of_list equal_windows) wd.wd_document.dc_dom.dm_body

let get_all_referred_windows trace =
  List.fold_left IndexWindowSet.union IndexWindowSet.empty @@
    List.map (fun s -> get_referred_windows s.st_window trace.global) trace.states

let unique_idxs wds =
  let idxs = IndexWindowSet.elements wds |> List.map fst in
  List.sort_uniq Int.compare idxs = List.sort Int.compare idxs

let merge_collisions traceA traceB =
  let open IndexWindowSet in
  let rwdsA = get_all_referred_windows traceA in
  let rwdsB = get_all_referred_windows traceB in
  assert (unique_idxs rwdsA && unique_idxs rwdsB);
  let collisions = List.concat_map (fun (i, w) ->
                       Option.bind (List.assoc_opt i @@ elements rwdsB) (fun w' ->
                           if Types.Window.equal w w' then None else Some (i, w'))
                       |> Option.to_list) (elements rwdsA) in
  let next_id = List.concat_map IndexWindowSet.elements [rwdsA; rwdsB]
                |> List.fold_left (fun acc (i, _) -> if acc <= i then i else acc) 0
                |> Int.add 1 in
  let replace_window_idx oldi newi wd =
    let open UpdateBrowser in
    update_wd_document wd  @@ fun dc ->
    update_dc_dom dc       @@ fun dm ->
    update_dm_body dm      @@
    List.map (fun (idx, oelm) ->
        idx, Option.map (fun elm ->
                 match elm with
                 | DOMElementResource (url, ContentElementFrame (frame, html)) when frame.frame_window = oldi ->
                    DOMElementResource (url, ContentElementFrame ({ frame with frame_window = newi }, html))
                 | elm -> elm)
               oelm)
  in
  let replace_state_idx oldi newi state =
    let open UpdateBrowser in
    update_st_window state @@ fun wd ->
    replace_window_idx oldi newi wd
  in
  let replace_event_idx oldi newi event =
    match event with
    | EvResponse (rp, corr) ->
       EvResponse ({ rp with rp_content =
                               (match rp.rp_content with
                                | Some (ContentElementFrame (frm, html)) when frm.frame_window = oldi ->
                                   Some (ContentElementFrame ( { frm with frame_window = newi }, html))
                                | cnt -> cnt) }, corr)
    | EvScriptNavigateFrame (p1, p2, frm, url) when frm.frame_window = oldi ->
       EvScriptNavigateFrame (p1, p2, { frm with frame_window = newi }, url)
    | EvScriptUpdateHTML (sc, pt, wd) ->
       EvScriptUpdateHTML (sc, pt, replace_window_idx oldi newi wd)
    | _ -> event
  in
  let update_trace (trace, next_idx) (idx, wd) =
    { global = { trace.global with windows = (next_idx, wd) :: List.remove_assoc idx trace.global.windows }
    ; states = List.map (replace_state_idx idx next_idx) trace.states
    ; events = List.map (replace_event_idx idx next_idx) trace.events
    }
    , next_idx + 1
  in
  traceA, fst @@ List.fold_left update_trace (traceB, next_id) collisions


let merge_traces before after =
  let before, after = merge_collisions before after in
  let merged_global =
    let windows_union = IndexWindowSet.union (get_all_referred_windows before) (get_all_referred_windows after) in
    let def_value = List.assoc (-1) after.global.windows in
    assert (unique_idxs windows_union);
    { after.global with windows = (-1, def_value) :: IndexWindowSet.elements windows_union }
  in
  assert (Types.State.equal (List.hd (List.rev before.states)) (List.hd after.states));
  { events = after.events
  ; states = before.states @ List.tl after.states
  ; global = merged_global
  }
