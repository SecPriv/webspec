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
Require Import BrowserLemmas.

Require Import Coq.Lists.List.
Import List.ListNotations.


Definition HostInvariantSC (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall pt sc ctx c_idx cookie cname h _evs,
    Reachable gb evs st ->
    (* A script is setting a cookie *)
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    evs = (EvScriptSetCookie pt (DOMPath [] DOMTopLevel) c_idx cookie :: _evs) ->
    (* The cookie prefix is __Host *)
    (sc_name cookie) = (Host cname) ->
    (* The cookie has been registered in the script context *)
    url_host (wd_location ctx) = Some h ->
    (sc_reg_domain cookie) = h.

Definition HostInvariantRP (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall rp corr cookie _evs cname h,
    Reachable gb evs st ->
    (* A response is setting a cookie *)
    evs = (EvResponse rp corr :: _evs) ->
    (rp_hd_set_cookie (rp_headers rp)) = Some cookie ->
    (* The cookie prefix is __Host *)
    (sc_name cookie) = (Host cname) ->
    (* The cookie has been registered by the domain of rp *)
    url_host (rp_url rp) = Some h ->
    (sc_reg_domain cookie) = h.

Definition HostInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall rp corr pt sc ctx c_idx cookie _evs cname h,
    Reachable gb evs st ->
    (
      (
        evs = (EvResponse rp corr :: _evs) /\
        (rp_hd_set_cookie (rp_headers rp)) = Some cookie /\
        (sc_name cookie) = (Host cname) /\
        url_host (rp_url rp) = Some h
      ) \/
      (
        is_script_in_dom_path gb (st_window st) pt sc ctx /\
        evs = (EvScriptSetCookie pt (DOMPath [] DOMTopLevel) c_idx cookie :: _evs) /\
        (sc_name cookie) = (Host cname) /\
        url_host (wd_location ctx) = Some h
      )
    ) ->
    (sc_reg_domain cookie) = h.


Theorem equiv_HostInvariant_RP_SC :
  forall gb evs st,
    HostInvariant gb evs st <-> (HostInvariantRP gb evs st /\ HostInvariantSC gb evs st).
Proof.
  intros gb evs st; split; unfold HostInvariant, HostInvariantSC, HostInvariantRP;
  [ intro HHost; split | intro HHost; destruct HHost as (HHostRP, HHostSC) ];
  intros.
  - apply (HHost rp corr (DOMPath [] DOMTopLevel) (Build_Script initial_url 0) initial_window 0 cookie _evs cname h H);
    left; auto.
  - apply (HHost initial_response 0 pt sc ctx c_idx cookie _evs cname h H);
    right; auto.
  - destruct H0 as [ (H0, (H1, (H2, H3))) | (H0, (H1, (H2, H3))) ].
    + apply (HHostRP rp corr cookie _evs cname h H); auto.
    + apply (HHostSC pt sc ctx c_idx cookie cname h _evs H); auto.
Qed.


(* Fix with:
    c_domain_relaxation (config gb) = false ->
*)
Inductive HostQuerySC (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall pt sc ctx c_idx cookie cname h _evs,
    Reachable gb evs st ->
    (* A script is setting a cookie *)
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    evs = (EvScriptSetCookie pt (DOMPath [] DOMTopLevel) c_idx cookie :: _evs) ->
    (* The cookie prefix is __Host *)
    (sc_name cookie) = (Host cname) ->
    url_host (wd_location ctx) = Some h ->
    (* The cookie has not been registered in the context of the script *)
    (sc_reg_domain cookie) <> h ->
    HostQuerySC gb evs st.


Theorem HostQuerySC_invalidate_HostInvariant :
  forall gb evs st,
    HostQuerySC gb evs st -> HostInvariant gb evs st -> False.
Proof.
  intros gb evs st HQuerySC HInvariant.
  unfold HostInvariant in HInvariant; destruct HQuerySC.
  apply H4; apply (HInvariant initial_response 0 pt sc ctx c_idx cookie _evs cname h H);
  right; auto.
Qed.


Lemma update_window_on_response_path :
  forall gb st pt_rp rp wd pt_ctx ctx,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp pt_rp (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx', window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx /\ wd_location ctx' = wd_location ctx)
    \/ wd_location ctx = rp_url rp.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_rp,ds_rp) rp wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_window_on_response_inversion _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|[H|H]]].
  - left; exists ctx...
  - destruct H as (ctx',(wd_idx',(Hwindow',Hrender'))); destruct ds_rp;
    destruct Hrender' as (H1,(H2,(H3,(H4,(H5,H6)))));
    destruct (rp_content rp); try contradiction; destruct H6 as (H6,H7)...
    + destruct c; try contradiction; destruct H7 as (H7,H8);
      right...
    + destruct (html_body (dc_html (wd_document ctx')).[dm_pt_index]); try contradiction; destruct H7 as (H7,(H8,H9));
      left; exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    left; exists ctx'...
  - destruct H as (ctx'',(ctx',(frm_idx',(frm',(frm_htrml',(frm_wd_idx',(Hcontent',(Hframe',Hrender'))))))))...
    destruct Hrender' as (H1,(H2,(H3,(H4,(H5,H6)))));
    destruct (rp_content rp); try contradiction; destruct H6 as (H6,H7);
    destruct (html_body (dc_html (wd_document ctx'')).[frm_idx']); try contradiction; destruct H7 as (H7,(H8,H9));
    injection Hcontent'; clear Hcontent'; intros...
    destruct H8 as (H8,H9); destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hframe') as (u_,(H_,H__)); injection H_; clear H_; intros...
    rewrite H9; right...
Qed.


Lemma update_window_html_path :
  forall gb st pt_cx cx html wd pt_ctx ctx,
    update_window_html_from_ctx gb (st_version st) cx html pt_cx (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx', window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx /\ wd_location ctx' = wd_location ctx).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_cx,ds_cx) cx html wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_window_html_from_ctx_inversion _ _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx...
  - destruct H as (ctx',(wd_idx',(Hwindow',Hupdate')));
    exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'...
Qed.


Lemma update_html_initiator_path :
  forall gb st pt_init init wd pt_ctx ctx,
    update_html_req_initiator gb (st_version st) init pt_init (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx', window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx /\ wd_location ctx' = wd_location ctx).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_init,ds_init) init wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_html_req_initiator_inversion _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx...
  - destruct H as (ctx',(idx',(Hwindow',Hupdate')));
    exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'...
Qed.


Lemma update_window_domain_path :
  forall gb st pt_cx cx domain wd pt_ctx ctx,
    update_window_domain_from_ctx gb (st_version st) cx domain pt_cx (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx', window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx /\ wd_location ctx' = wd_location ctx).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_cx,ds_cx) cx domain wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_window_domain_from_ctx_inversion _ _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx...
  - destruct H as (ctx',(Hwindow',Hupdate'));
    exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'...
Qed.


Lemma is_valid_window_context_location :
  forall gb evs st pt ctx,
    Reachable gb evs st ->
    window_ctx_of_dom_path_rec gb ctx (st_window st) pt ->
    is_valid_url (wd_location ctx).
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st (ls,pt) ctx Hreachable; generalize ctx; clear ctx; induction Hreachable; intros ctx Hwindow...
  - inversion Hwindow. injection H3; clear H3; intros; firstorder...
    unfold is_frame_window_at_page_index in H3;
    unfold is_frame_at_page_index in H3; firstorder...
  - pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}}).
    destruct (update_window_on_response_path _ st _ _ _ _ _ H0 Hwindow) as [ (ctx',(H2,H3)) | H2]...
    + rewrite <- H3; apply (IHHreachable ctx')...
    + rewrite H2; apply (is_valid_url_response _ _ st _ Hreachable (update_window_on_response_fetch_engine _ st _ _ _ H0)).
  - pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (update_html_initiator_path _ st _ _ st_wd_2 _ _ H5 Hwindow) as (ctx',(Hctx',Heq));
    rewrite <- Heq; clear Heq;
    pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (update_window_html_path _ st_ _ _ _ _ _ _ H4 Hctx') as (ctx'',(Hctx'',Heq));
    rewrite <- Heq; clear Heq...
  - pose (st_ := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (update_html_initiator_path _ st_ _ _ _ _ _ H5 Hwindow) as (ctx',(Hctx',Heq));
    rewrite <- Heq; clear Heq;
    pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (update_window_html_path _ st _ _ _ _ _ _ H3 Hctx') as (ctx'',(Hctx'',Heq));
    rewrite <- Heq; clear Heq...
  - pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (update_window_domain_path _ st _ _ _ _ _ _ H2 Hwindow) as (ctx',(Hctx',Heq));
    rewrite <- Heq; clear Heq...
Qed.


Theorem fix_HostInvariantSC :
  forall gb evs st,
    c_domain_relaxation (config gb) = false -> HostInvariantSC gb evs st.
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st Hdomain pt sc ctx c_idx cookie cname h _evs Hreachable Hin_dom Hevs Hsc_name Hurl_host...
  inversion Hin_dom as [_ _ Hwindow_ctx _ _].
  pose (no_relaxation_implies_empty_top_domain _ _ _ Hdomain Hreachable) as Hrelax.
  assert (is_valid_url (wd_location ctx)) as Hvalid_url
  by apply (is_valid_window_context_location _ _ _ pt ctx Hreachable Hwindow_ctx).
  inversion Hreachable; firstorder; inversion H7...
  destruct (eq_is_script_in_dom_path gb pt st_wd sc0 wd_ctx sc ctx H6 Hin_dom)...
  (* unfold is_same_origin_window_domain ctx st_wd and use the fact that wd_document_domain st_wd = None *)
  unfold is_same_origin_window_domain in H13; rewrite Hrelax in H13;
  destruct (wd_document_domain ctx); try contradiction...
  (* unfold is_valid_setcookie (wd_location st_wd) cookie and use the that sc_name cookie = Host cname *)
  unfold is_valid_setcookie in H14; rewrite Hsc_name in H14; firstorder...
  (* unfold check_secure_protocol (wd_location st_wd) cookie *)
  unfold check_secure_protocol in H1; unfold checkb_secure_protocol in H1; unfold is_true in H1; rewrite H0 in H1;
  destruct (Equality.eqb_eq Protocol (url_protocol (wd_location st_wd)) ProtocolHTTPS) as (Heq_protocol,_);
  specialize (Heq_protocol H1)...
  (* use the fact that url_protocol (wd_location st_wd) = ProtocolHTTPS in origin_of_url (wd_location st_wd) *)
  unfold origin_of_url in *; rewrite Heq_protocol in H11...
  (* case analysis of url_protocol (wd_location ctx), ProtocolHTTP is automatically discarded *)
  unfold is_valid_url in Hvalid_url; remember (url_protocol (wd_location ctx)) as url_protocol;
  destruct url_protocol...
  (* ProtocolHTTPS *)
  - injection H11; clear H11; intros...
    rewrite <- H14 in H9; rewrite Hurl_host in H9...
  (* ProtocolData *)
  - destruct (url_path (wd_location ctx))...
  (* ProtocolBlob *)
  - destruct (url_path (wd_location ctx));
    destruct (url_host (wd_location ctx));
    try contradiction...
Qed.


InlineRelation is_secure_context             With Depth 1.
InlineRelation is_not_secure_context         With Depth 0.
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
Extract Query HostQuerySC Using Lemma extracted_lemma_hostquery_state12.
