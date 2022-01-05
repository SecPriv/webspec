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


Definition CORSInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall em rq corr scr_idx scr_pt rp rp_corr em_idx _evs,
    Reachable gb evs st ->
    (* Non-simple request made by a script *)
    evs = (EvRequest em rq corr :: _evs) ->
    em = EmitterScript scr_idx scr_pt /\ (emitters gb).[em_idx] = em ->
    is_cross_origin_request (st_window st) rq ->
    not (is_cors_simple_request rq) ->
    (* Get CORS preflight response *)
    is_cors_authorization_response gb st em_idx rq corr rp rp_corr ->
    (* The auth. comes from rq_url *)
    origin_of_url (rq_url rq) = origin_of_url (rp_url rp).


(* Fix the issue by disabling preflight redirection with:
   c_redirect_preflight_requests (config gb) = false ->
*)
Inductive CORSQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall em rq corr scr_idx scr_pt rp rp_corr em_idx _evs,
    Reachable gb evs st ->
    (* Non-simple request made by a script *)
    evs = (EvRequest em rq corr :: _evs) ->
    em = EmitterScript scr_idx scr_pt /\ (emitters gb).[em_idx] = em ->
    is_cross_origin_request (st_window st) rq ->
    not (is_cors_simple_request rq) ->
    (* Get CORS preflight response *)
    is_cors_authorization_response gb st em_idx rq corr rp rp_corr ->
    (* The auth. does not come from rq_url *)
    origin_of_url (rq_url rq) <> origin_of_url (rp_url rp) ->
    CORSQuery gb evs st.


Theorem CORSQuery_invalidate_CORSInvariant :
  forall gb evs st (x:CORSQuery gb evs st),
    CORSInvariant gb evs st -> False.
Proof.
  intros.
  unfold CORSInvariant in H.
  destruct x.
  specialize (H em rq corr scr_idx scr_pt rp rp_corr em_idx _evs H0 H1 H2 H3 H4 H5).
  congruence.
Qed.


InlineRelation is_secure_context             With Depth 0.
InlineRelation window_ctx_of_dom_path_rec    With Depth 0.
InlineRelation window_ctx_of_dom_path        With Depth 0.
InlineRelation is_script_in_dom_path         With Depth 0.
InlineRelation is_form_in_dom_path           With Depth 0.
InlineRelation update_window_on_response     With Depth 0.
InlineRelation update_window_html_from_ctx   With Depth 0.
InlineRelation update_window_domain_from_ctx With Depth 0.
InlineRelation update_html_req_initiator     With Depth 0.
InlineRelation is_valid_setcookie_from_ctx   With Depth 0.
InlineRelation in_redirect_history           With Depth 2.
InlineRelation Scriptstate                   With Depth 5.

Set Array Size 5.
Extract Query CORSQuery Using Lemma script_state_is_reachable.
