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

Require Import Browser.
Require Import BrowserStates.

Require Import Coq.Lists.List.
Import List.ListNotations.


Definition TTInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall pt target_pt target_ctx ssrc ttypes,
    Reachable gb evs st ->
    (* The target context has Trusted-Types enabled *)
    url_protocol (wd_location target_ctx) = ProtocolHTTPS ->
    rp_hd_csp (dc_headers (wd_document target_ctx)) =
    Some {| csp_script_src := ssrc; csp_trusted_types := Some ttypes |} ->
    tt_policy ttypes = Some None ->
    tt_require_for_script ttypes = true ->
    (* No script can update the dom using innerHTML *)
    not (In (EvScriptUpdateHTML pt target_pt target_ctx) evs).


(* Add this for TT Colluding inconsistency *)
(* (c_restrict_tt_to_secure_contexts (config gb)) = false -> *)
Inductive TTQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall (pt: NestedDOMPath) sc ctx target_pt target_ctx target_ctx_after ssrc ttypes _evs,
     c_tt_strict_realm_check (config gb) = false ->
     c_restrict_tt_to_secure_contexts (config gb) = true ->

    Reachable gb evs st ->
    (* A script is updating the dom using innerHTML *)
    evs = (EvScriptUpdateHTML pt target_pt target_ctx :: _evs) ->
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    window_ctx_of_dom_path gb (st_window st) target_pt target_ctx_after ->
    (* The target context has Trusted-Types *)
    url_protocol (wd_location target_ctx) = ProtocolHTTPS ->
    rp_hd_csp (dc_headers (wd_document target_ctx)) = Some (Build_CSP ssrc (Some ttypes)) ->
    tt_policy ttypes = Some None ->
    tt_require_for_script ttypes = true ->
    TTQuery gb evs st.


Theorem TTQuery_invalidate_TTInvariant :
  forall gb evs st (x:TTQuery gb evs st),
    TTInvariant gb evs st -> False.
Proof.
  intros.
  unfold TTInvariant in H.
  destruct x.
  specialize (H pt target_pt target_ctx _ _ H2 H6 H7 H8 H9).
  apply H. subst. intuition.
Qed.


Require Import Coq.Logic.Classical_Prop.

Lemma cannot_update_html_if_tt_enabled :
  forall gb,
    c_tt_strict_realm_check (config gb) = true ->
    c_restrict_tt_to_secure_contexts (config gb) = false ->
  forall st evs pt target_pt target_ctx ssrc,
    Reachable gb evs st ->
    (* The target context has Trusted-Types *)
    url_protocol (wd_location target_ctx) = ProtocolHTTPS ->
    rp_hd_csp (dc_headers (wd_document target_ctx)) =
    Some {| csp_script_src := ssrc;
            csp_trusted_types := Some {|
                                     tt_policy := Some None;
                                     tt_require_for_script := true |}
         |} ->
    (* No script can update the dom using innerHTML *)
    not (In (EvScriptUpdateHTML pt target_pt target_ctx) evs).
Proof with simpl in *; firstorder; try congruence.
  intros.
  induction H1; unfold not...
  - (* script update html *)
    simpl in *.
    assert (target_ctx = target_ctx0) by congruence.
    rewrite H12 in *.
    assert (target_ctx = target_ctx0) by congruence.
    rewrite <- H13 in *.
    rewrite H3 in H7.
    rewrite H0 in H7.
    rewrite H in H8.
    rewrite H8 in H7.
    assert (scriptstate_c: forall gb st sc realm elt,
               Scriptstate gb st sc (SOTrustedHTML realm elt) ->
               exists c, c = (SOTrustedHTML realm elt)
                         /\ Scriptstate gb st sc c). intros...
    apply scriptstate_c in H7.
    destruct H7.
    destruct H7.

    induction H14...
    * assert (wd_ctx0 = target_ctx) by congruence.
      subst. rewrite H3 in H15...
Qed.

Theorem strict_realm_check_implies_invariant :
  forall gb evs st,
  c_tt_strict_realm_check (config gb) = true ->
  c_restrict_tt_to_secure_contexts (config gb) = false ->
  TTInvariant gb evs st.
Proof with simpl in *; firstorder; try congruence.
  intros.
  unfold TTInvariant.
  intros.
  apply cannot_update_html_if_tt_enabled with (gb := gb) (st := st) (ssrc := ssrc)...
  destruct H4,H5...
Qed.


InlineRelation is_not_secure_context         With Depth 1.
InlineRelation is_secure_context             With Depth 1.
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

Set Array Size 5.
Extract Query TTQuery.
