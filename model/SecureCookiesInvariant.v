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
From Extractor Require Import Equality.

Require Import Browser.

Require Import Coq.Lists.List.
Import List.ListNotations.


Definition SecureCookiesInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall rp corr _evs cookie,
    Reachable gb evs st ->
    evs = (EvResponse rp corr :: _evs) ->
    rp_hd_set_cookie (rp_headers rp) = Some cookie ->
    sc_secure cookie = true ->
    url_protocol (rp_url rp) = ProtocolHTTPS.

Definition SecureCookiesInvariantSC (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall pt target target_ctx c_idx cookie _evs,
    Reachable gb evs st ->
    evs = (EvScriptSetCookie pt target c_idx cookie :: _evs) ->
    sc_secure cookie = true ->
    window_ctx_of_dom_path gb (st_window st) target target_ctx ->
    url_protocol (wd_location target_ctx) = ProtocolHTTPS.


Theorem secure_cookies_invariant_response :
  forall gb evs st, SecureCookiesInvariant gb evs st.
Proof.
  unfold SecureCookiesInvariant.
  intros.
  induction H; try congruence.
  assert (rp = (responses gb.[rp_idx])). congruence.
  subst.
  rewrite H1 in H9.
  unfold is_valid_setcookie in H9.
  unfold check_secure_protocol in H9.
  unfold checkb_secure_protocol in H9.
  unfold implb in H9.
  rewrite H2 in *.
  destruct (sc_name cookie).
  - destruct H9, H3, H9.
    apply -> Equality.eqb_eq in H9. apply H9.
  - destruct H9, H3, H9, H10.
    apply -> Equality.eqb_eq in H10. apply H10.
  - destruct H9, H3, H9, H10.
    apply -> Equality.eqb_eq in H10. apply H10.
Qed.


Inductive SecureCookiesQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall rp corr _evs cookie,
    Reachable gb evs st ->
    evs = (EvResponse rp corr :: _evs) ->
    rp_hd_set_cookie (rp_headers rp) = Some cookie ->
    sc_secure cookie = true ->
    url_protocol (rp_url rp) <> ProtocolHTTPS ->
    SecureCookiesQuery gb evs st.

Inductive SecureCookiesQuerySC (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state_sc : forall pt target target_ctx c_idx cookie _evs,
    Reachable gb evs st ->
    evs = (EvScriptSetCookie pt target c_idx cookie :: _evs) ->
    sc_secure cookie = true ->
    window_ctx_of_dom_path gb (st_window st) target target_ctx ->
    url_protocol (wd_location target_ctx) <> ProtocolHTTPS ->
    SecureCookiesQuerySC gb evs st.


InlineRelation is_secure_context             With Depth 2.
InlineRelation is_not_secure_context         With Depth 2.
InlineRelation window_ctx_of_dom_path_rec    With Depth 2.
InlineRelation window_ctx_of_dom_path        With Depth 2.
InlineRelation is_script_in_dom_path         With Depth 2.
InlineRelation is_form_in_dom_path           With Depth 2.
InlineRelation update_window_on_response     With Depth 2.
InlineRelation update_window_html_from_ctx   With Depth 2.
InlineRelation update_window_domain_from_ctx With Depth 2.
InlineRelation update_html_req_initiator     With Depth 2.
InlineRelation is_valid_setcookie_from_ctx   With Depth 2.
InlineRelation in_redirect_history           With Depth 2.
InlineRelation Scriptstate                   With Depth 5.
Extract Query SecureCookiesQuery.
