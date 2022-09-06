(********************************************************************************)
(*  Copyright (c) 2021 Lorenzo Veronese & Benjamin Farinier                     *)
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

Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.

Require Import Browser.
Require Import BrowserStates.

Require Import Coq.Lists.List.
Import List.ListNotations.


Definition LSInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall evs pt _evs frm fhtml fwd ctx lv pt_idx init_idx,
    let get_csp wd :=
        rp_hd_csp (dc_headers (wd_document wd)) in
    Reachable gb evs st ->
    (* A document has just been loaded in a frame *)
    evs = (EvDOMUpdate pt :: _evs) ->
    is_frame_in_dom_path gb (st_window st) pt frm fhtml fwd ctx ->
    is_local_scheme (wd_location fwd) ->
    (* get navigation initiator *)
    pt = DOMPath lv (DOMIndex pt_idx) ->
    is_wd_initiator_of_idx ctx pt_idx (Some init_idx) ->
    (* The csp is equal to the req. initiator *)
    get_csp fwd = get_csp (windows gb.[init_idx]).


Inductive LSQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state2 : forall (pt : NestedDOMPath) (_evs : list Event) (frm : Frame) (fhtml : HTML) (fwd ctx : Window) (lv : list nat) (pt_idx init_idx : nat),
    Reachable gb evs st ->

    (* Change these values to change the model behavior *)
    c_csp_inherit_local_from_initiator (config gb) = true ->
    c_csp_inherit_blob_from_creator (config gb) = true ->

    (* A document has just been loaded in a frame *)
    evs = (EvDOMUpdate pt :: _evs) ->
    is_frame_in_dom_path gb (st_window st) pt frm fhtml fwd ctx ->
    is_local_scheme (wd_location fwd) ->
    (* get request initiator *)
    pt = DOMPath lv (DOMIndex pt_idx) ->
    in_body (dc_init (wd_document ctx)).[pt_idx] = Some init_idx ->
    (* The csp is equal to the req. initiator *)
    rp_hd_csp (dc_headers (wd_document fwd)) <>
    rp_hd_csp (dc_headers (wd_document (windows gb.[init_idx]))) ->
    LSQuery gb evs st.


Theorem LSQuery_invalidate_LSInvariant :
  forall gb evs st,
    LSQuery gb evs st -> LSInvariant gb evs st -> False.
Proof.
  intros gb evs st LSQuery LocScInvariant.

  unfold LSInvariant in LocScInvariant; destruct LSQuery.
  specialize (LocScInvariant evs pt _evs frm fhtml fwd ctx lv pt_idx init_idx H H2 H3 H4 H5 H6).
  congruence.
Qed.


InlineRelation is_frame_at_page_index.
InlineRelation is_secure_context             With Depth 1.
InlineRelation is_not_secure_context         With Depth 1.
InlineRelation window_ctx_of_dom_path_rec    With Depth 1.
InlineRelation window_ctx_of_dom_path        With Depth 1.
InlineRelation is_script_in_dom_path         With Depth 1.
InlineRelation is_form_in_dom_path           With Depth 1.
InlineRelation update_window_on_response     With Depth 1.
InlineRelation update_window_html_from_ctx   With Depth 1.
InlineRelation update_window_domain_from_ctx With Depth 1.
InlineRelation update_html_req_initiator     With Depth 1.
InlineRelation is_valid_setcookie_from_ctx   With Depth 1.
InlineRelation in_redirect_history           With Depth 2.
InlineRelation Scriptstate                   With Depth 5.


Set Array Size 7.
Extract Query LSQuery Using Lemma iframe_sameorigin_script_state_is_reachable.
