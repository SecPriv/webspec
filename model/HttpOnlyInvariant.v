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


Definition HttpOnlyInvariant (gb: Global) (evs: list Event) (st: State) : Prop  :=
  forall sc cm c_idx cookie,
    Reachable gb evs st ->
    (* A script has access to the cookie cm *)
    Scriptstate gb st sc (SOCookie c_idx cm) ->
    (* The cookie is not httponly *)
    st_cookiejar st.[c_idx] = Some cookie ->
    cj_http_only cookie = false.


(* Fix the issue by enabling forbidden headers with:
   (c_forbidden_headers (config gb)) = true ->
*)
Inductive HttpOnlyQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall sc cm c_idx cookie,
    Reachable gb evs st ->
    (* A script has access to the cookie cm *)
    Scriptstate gb st sc (SOCookie c_idx cm) ->
    (* The cookie is httponly *)
    st_cookiejar st.[c_idx] = Some cookie ->
    cm_name cm = sc_name cookie /\ cm_value cm = sc_value cookie ->
    sc_http_only cookie = true ->
    HttpOnlyQuery gb evs st.


Theorem HttpOnlyQuery_invalidate_HttpOnlyInvariant :
  forall gb evs st (x:HttpOnlyQuery gb evs st),
    HttpOnlyInvariant gb evs st -> False.
Proof.
  intros.
  unfold HttpOnlyInvariant in H.
  destruct x.
  specialize (H sc cm c_idx cookie H0 H1 H2).
  unfold cj_http_only in H.
  congruence.
Qed.


InlineRelation is_secure_context             With Depth 0.
InlineRelation is_not_secure_context         With Depth 0.
InlineRelation window_ctx_of_dom_path_rec    With Depth 0.
InlineRelation window_ctx_of_dom_path        With Depth 0.
InlineRelation is_script_in_dom_path         With Depth 0.
InlineRelation is_form_in_dom_path           With Depth 0.
InlineRelation update_window_on_response     With Depth 0.
InlineRelation update_window_html_from_ctx   With Depth 0.
InlineRelation update_window_domain_from_ctx With Depth 0.
InlineRelation is_valid_setcookie_from_ctx   With Depth 0.
InlineRelation update_html_req_initiator     With Depth 0.
InlineRelation in_redirect_history           With Depth 2.
InlineRelation Scriptstate                   With Depth 5.

Set Array Size 5.
Extract Query HttpOnlyQuery Using Lemma script_state_is_reachable.
