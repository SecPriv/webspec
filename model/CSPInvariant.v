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

Require Import Arith.PeanoNat.
Require Import Coq.Lists.List.
Import List.ListNotations.


Definition CSPInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall pt sc ctx pt_u src origin tctx tt _evs,
    Reachable gb evs st ->
    (* A script sc is present in the page *)
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    (* The DOM of the toplevel window has been modified by sc *)
    evs = (EvScriptUpdateHTML pt (DOMPath [] pt_u) tctx :: _evs ) ->
    (* The toplevel window is protected by CSP *)
    rp_hd_csp (dc_headers (wd_document (st_window st))) =
    Some {| csp_script_src := Some src; csp_trusted_types := tt |} ->
    (* The script sc is allowed by the CSP *)
    origin_of_url (wd_location (st_window st)) = Some origin ->
    csp_src_match src origin (script_src sc).


(* Fix with:
    c_origin_wide_csp (config gb) = true ->
    c_domain_relaxation (config gb) = false ->
*)
Inductive CSPQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall pt sc ctx pt_u src origin tctx tt _evs,
    Reachable gb evs st ->
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    (* The toplevel window is protected by CSP *)
    rp_hd_csp (dc_headers (wd_document (st_window st))) = Some (Build_CSP (Some src) tt) ->
    (* The script sc is not allowed by the CSP *)
    origin_of_url (wd_location (st_window st)) = Some origin ->
    not (csp_src_match src origin (script_src sc)) ->
    (* The DOM of the toplevel window has been modified by `sc` *)
    evs = (EvScriptUpdateHTML pt (DOMPath [] pt_u) tctx :: _evs ) ->
    CSPQuery gb evs st.


Theorem CSPQuery_invalidate_CSPInvariant :
  forall gb evs st, CSPQuery gb evs st -> CSPInvariant gb evs st -> False.
Proof.
  intros gb evs st Hquery H.
  unfold CSPInvariant in H.
  destruct Hquery.
  specialize (H _ _ _ _ _ _ _ _ _ H0 H1 H5 H2 H3).
  congruence.
Qed.


Definition CSP_subsume rp_hd1 rp_hd2 : Prop :=
  rp_hd_csp rp_hd1 = None \/ rp_hd_csp rp_hd1 = rp_hd_csp rp_hd2.


Lemma CSP_subsume_trans :
  forall rp_hd1 rp_hd2 rp_hd3,
  CSP_subsume rp_hd1 rp_hd2 ->
  CSP_subsume rp_hd2 rp_hd3 ->
  CSP_subsume rp_hd1 rp_hd3.
Proof with subst; simpl in *; auto; try congruence.
  unfold CSP_subsume.
  intros rp_hd1 rp_hd2 rp_hd3 [H12sc|H12sc] [H23sc|H23sc];
  unfold CSP_subsume in *; (left; subst; congruence) || (right; subst; congruence)...
Qed.


Lemma CSP_subsume_src_match :
  forall wd ctx csp_wd csp_tt origin src,
    CSP_subsume (dc_headers (wd_document wd)) (dc_headers (wd_document ctx)) ->
    rp_hd_csp (dc_headers (wd_document wd)) = Some (Build_CSP (Some csp_wd) csp_tt)  ->
    exists csp_ctx csp_ctx_tt,
      (rp_hd_csp (dc_headers (wd_document ctx)) = Some (Build_CSP (Some csp_ctx) csp_ctx_tt)
       /\ (csp_src_match csp_ctx origin src ->
           csp_src_match csp_wd origin src)).
Proof with subst; simpl in *; auto; try congruence.
  intros wd ctx csp_wd csp_tt origin csp [Hsc|Hsc] Hsrc;
    exists csp_wd; exists csp_tt; split...
Qed.


Lemma update_window_html_from_ctx_header :
  forall gb st pt_cx cx html wd pt_ctx ctx,
    update_window_html_from_ctx gb (st_version st) cx html pt_cx (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx',
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ dc_headers (wd_document ctx) = dc_headers (wd_document ctx')
       /\ origin_of_url (wd_location ctx) = origin_of_url (wd_location ctx')).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_cx,ds_cx) cx html wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_window_html_from_ctx_inversion _ _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx...
  - destruct H as (ctx',(wd_idx',(Hwindow',Hupdate')));
    exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'...
Qed.


Lemma update_html_req_initiator_header :
  forall gb st pt_init init wd pt_ctx ctx,
    update_html_req_initiator gb (st_version st) init pt_init (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    (exists ctx',
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ dc_headers (wd_document ctx) = dc_headers (wd_document ctx')
       /\ origin_of_url (wd_location ctx) = origin_of_url (wd_location ctx')).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_init,ds_init) init wd (ls_ctx,ds_ctx) ctx Hupdate Hwindow;
  destruct (update_html_req_initiator_inversion _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx...
  - destruct H as (ctx',(wd_idx',(Hwindow',Hupdate')));
    exists ctx'...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'...
Qed.


Lemma is_script_update_html :
  forall gb st pt_cx cx html wd pt_sc sc ctx,
    update_window_html_from_ctx gb (st_version st) cx html pt_cx (st_window st) wd ->
    is_script_in_dom_path gb wd pt_sc sc ctx ->
    exists ctx',
      (is_script_in_dom_path gb (st_window st) pt_sc sc ctx'
      /\ rp_hd_csp (dc_headers (wd_document ctx)) = rp_hd_csp (dc_headers (wd_document ctx'))
      /\ origin_of_url (wd_location ctx) = origin_of_url (wd_location ctx')).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_cx,ds_cx) cx html wd (ls_sc,ds_sc) sc ctx Hupdate Hscript.
  destruct Hscript as (idx,lst,Hwindow,H,Hscript); injection H; clear H; intros...
  destruct (update_window_html_from_ctx_inversion _ _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx; split...
    apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
  - destruct H as (ctx',(wd_idx',(Hwindow',Hupdate')));
    exists ctx'; split...
    destruct (Nat.eq_dec wd_idx' idx) as [Heq|Hnq]...
    + destruct (content_script_at_page_index _ _ _ _ Hscript); destruct html; congruence.
    + apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
      apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript)...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'; split...
    destruct (Nat.eq_dec frm_idx' idx) as [Heq|Hnq]...
    + destruct (content_script_at_page_index _ _ _ _ Hscript); destruct html; congruence.
    + apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
      apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript)...
Qed.


Lemma is_script_update_initiator :
  forall gb st pt_init init wd pt_sc sc ctx,
    update_html_req_initiator gb (st_version st) init pt_init (st_window st) wd ->
    is_script_in_dom_path gb wd pt_sc sc ctx ->
    exists ctx',
      (is_script_in_dom_path gb (st_window st) pt_sc sc ctx'
      /\ rp_hd_csp (dc_headers (wd_document ctx)) = rp_hd_csp (dc_headers (wd_document ctx'))
      /\ origin_of_url (wd_location ctx) = origin_of_url (wd_location ctx')).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_init,ds_init) init wd (ls_sc,ds_sc) sc ctx Hupdate Hscript.
  destruct Hscript as (idx,lst,Hwindow,H,Hscript); injection H; clear H; intros...
  destruct (update_html_req_initiator_inversion _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx; split...
    apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
  - destruct H as (ctx',(idx',(Hwindow',Hupdate')));
    exists ctx'; split...
    apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'; split...
    destruct (Nat.eq_dec frm_idx' idx) as [Heq|Hnq]...
    + destruct (content_script_at_page_index _ _ _ _ Hscript); congruence.
    + apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
      apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript)...
Qed.


Lemma is_script_update_domain :
  forall gb st pt_cx cx domain wd pt_sc sc ctx,
    update_window_domain_from_ctx gb (st_version st) cx domain pt_cx (st_window st) wd ->
    is_script_in_dom_path gb wd pt_sc sc ctx ->
    exists ctx',
      (is_script_in_dom_path gb (st_window st) pt_sc sc ctx'
      /\ rp_hd_csp (dc_headers (wd_document ctx)) = rp_hd_csp (dc_headers (wd_document ctx'))
      /\ origin_of_url (wd_location ctx) = origin_of_url (wd_location ctx')).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls_cx,ds_cx) cx domain wd (ls_sc,ds_sc) sc ctx Hupdate Hscript.
  destruct Hscript as (idx,lst,Hwindow,H,Hscript); injection H; clear H; intros...
  destruct (update_window_domain_from_ctx_inversion _ _ _ _ _ _ _ _ Hupdate Hwindow) as [H|[H|H]].
  - exists ctx; split...
    apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
  - destruct H as (ctx',(Hwindow',Hupdate'));
    exists ctx'; split...
    apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
  - destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
    exists ctx'; split...
    destruct (Nat.eq_dec frm_idx' idx) as [Heq|Hnq]...
    + destruct (content_script_at_page_index _ _ _ _ Hscript); congruence.
    + apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
      apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript)...
Qed.


Lemma origin_wide_inv :
  forall gb evs st,
    c_origin_wide_csp (config gb) = true ->
    c_domain_relaxation (config gb) = false ->
    Reachable gb evs st ->
    forall pt ctx origin,
      window_ctx_of_dom_path_rec gb ctx (st_window st) pt ->
      origin_of_url (wd_location ctx) = Some origin ->
      exists idx,
        let '(origin', csp) := origin_csp gb.[idx] in
        origin = origin' /\
        rp_hd_csp (dc_headers (wd_document ctx)) = csp.
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st Hwide Hdomain Hreachable; induction Hreachable...
  - intros pt ctx origin Hwindow Horigin.
    unfold initial_window in Hwindow; inversion Hwindow...
    + exists 0; destruct (origin_csp gb.[0]) as (origin',csp); split...
    + exfalso; compute in H4; destruct H4...
  - intros (ls_ctx,ds_ctx) ctx origin Hwindow Horigin.
    rewrite Hwide in H; remember (origin_csp gb.[origin_idx]) as o;
      destruct o as (orig,csp)...
    pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    specialize (update_window_on_response_inversion _ st _ _ _ _ _ H0 Hwindow); destruct pt; intros [Hinv|[Hinv|[Hinv|Hinv]]]...
    + apply (IHHreachable (DOMPath ls_ctx ds_ctx) ctx origin Hinv Horigin).
    + destruct Hinv as (ctx',(wd_idx',(Hwindow',Hrender))).
      destruct Hrender as (H2,(H3,(H4,(H5,(H6,H7)))));
      destruct (rp_content rp); try contradiction; destruct H7 as (H7,H8); destruct dm_lv_pt...
      * destruct c; try contradiction; destruct H8 as (H8,H9)...
        rewrite Horigin in H; destruct H as (Hog,Hcsp);
        exists origin_idx; rewrite <- Heqo...
      * destruct (html_body (dc_html (wd_document ctx')).[dm_pt_index]); try contradiction; destruct H8 as (H8,(H9,H10))...
        apply (IHHreachable (DOMPath ls_ctx ds_ctx) ctx')...
    + destruct Hinv as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe,Hupdate))))))))...
      apply (IHHreachable (DOMPath ls_ctx ds_ctx) ctx')...
    + destruct Hinv as (ctx'',(ctx',(frm_idx',(frm',(frm_html',(frm_wd_idx',(Hcontent,(Hframe,Hrender))))))))...
      destruct Hrender as (H2,(H3,(H4,(H5,(H6,H7))))); destruct (rp_content rp); try contradiction; destruct H7 as (H7,H8);
      destruct (html_body (dc_html (wd_document ctx'')).[frm_idx']); try contradiction; destruct H8 as (H8,(H9,H10))...
      unfold is_frame_window_at_page_index in Hframe; unfold is_frame_at_page_index in Hframe; destruct Hframe as (Hframe,H_)...
      unfold Array.store in Hframe; unfold Array.select in Hframe; rewrite Nat.eqb_refl in Hframe;
      destruct c; try contradiction; destruct Hframe; destruct H9 as (H9,H12)...
      rewrite H12 in *... rewrite Horigin in H; destruct H as (H,H')...
      exists origin_idx; destruct (origin_csp gb.[origin_idx]) as (origin',csp'); split...
  - intros pt ctx origin Hwindow Horigin;
    pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (update_html_req_initiator_header _ st _ _ _ _ _ H5 Hwindow) as (ctx',(Hwindow_,(Hheader_,Horigin_)));
    pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (update_window_html_from_ctx_header _ st_ _ _ _ _ _ _ H4 Hwindow_) as (ctx'',(Hwindow__,(Hheader__,Horigin__)))...
    rewrite Hheader_ in *; rewrite Hheader__ in *;
    apply (IHHreachable pt ctx'' origin)...
  - intros pt ctx origin Hwindow Horigin;
    pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (update_html_req_initiator_header _ st _ _ _ _ _ H5 Hwindow) as (ctx',(Hwindow_,(Hheader_,Horigin_)));
    pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (update_window_html_from_ctx_header _ st_ _ _ _ _ _ _ H3 Hwindow_) as (ctx'',(Hwindow__,(Hheader__,Horigin__)))...
    rewrite Hheader_ in *; rewrite Hheader__ in *;
    apply (IHHreachable pt ctx'' origin)...
Qed.


Lemma origin_wide_implies_CSP_subsume_window_context :
  forall gb evs st,
    c_origin_wide_csp (config gb) = true ->
    c_domain_relaxation (config gb) = false ->
    Reachable gb evs st ->
    forall pt ctx,
      window_ctx_of_dom_path_rec gb ctx (st_window st) pt ->
      origin_of_url (wd_location (st_window st)) = origin_of_url (wd_location ctx) ->
      origin_of_url (wd_location (st_window st)) <> None ->
      CSP_subsume (dc_headers (wd_document (st_window st))) (dc_headers (wd_document ctx)).
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st Hwide Hdomain Hreachable pt ctx Hwindow Horigin1 Horigin2...
  case_eq (origin_of_url (wd_location (st_window st))); [ intros origin1 Heq1 | congruence];
  case_eq (origin_of_url (wd_location ctx)); [ intros origin2 Heq2 | congruence];
  destruct (origin_wide_inv _ _ _ Hwide Hdomain Hreachable (DOMPath [] DOMTopLevel) (st_window st) origin1 (Window_ctx_pt_base _ _ _ _ DOMTopLevel eq_refl eq_refl) Heq1) as (idx1,Hheader1);
  destruct (origin_wide_inv _ _ _ Hwide Hdomain Hreachable pt ctx origin2 Hwindow Heq2) as (idx2,Hheader2);
  remember (origin_csp gb.[idx1]) as o1; destruct o1 as (origin1',csp1);
  remember (origin_csp gb.[idx2]) as o2; destruct o2 as (origin2',csp2);
  destruct Hheader1 as (H1,Hcsp1);
  destruct Hheader2 as (H2,Hcsp2);
  rewrite Heq1 in Horigin1; rewrite Heq2 in Horigin1; injection Horigin1; clear Horigin1 Horigin2; intros...
  assert (idx1 = idx2) by (
    apply (array_distinct_inversion _ _ (distinct_origin_csp _ _ _ Hreachable));
    unfold Array.map; unfold Array.select in *;
    rewrite <- Heqo1; rewrite <- Heqo2;
    auto)...
  rewrite <- Heqo2 in Heqo1; injection Heqo1; clear Heqo1 Heqo2; intros; compute...
Qed.


Lemma script_match_csp_src :
  forall gb evs st pt sc ctx csp csp_tt origin,
    Reachable gb evs st ->
    is_script_in_dom_path gb (st_window st) pt sc ctx ->
    rp_hd_csp (dc_headers (wd_document ctx)) = Some (Build_CSP (Some csp) csp_tt) ->
    origin_of_url (wd_location ctx) = Some origin ->
    csp_src_match csp origin (script_src sc).
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st pt sc ctx csp csp_tt origin Hreachable; generalize pt sc ctx csp origin; clear pt sc ctx csp origin;
  induction Hreachable...
  - intros pt sc ctx csp origin Hscript Hheader Horigin;
    exfalso; inversion Hscript; inversion H3...
    injection H6; clear H6; intros...
    compute in H7; destruct H7...
  - intros pt_ sc ctx csp origin Hscript Hheader Horigin.
    inversion Hscript; rename H2 into Hwindow; rename H4 into Hscript_at_index...
    pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    specialize (update_window_on_response_inversion _ st _ _ _ _ _ H0 Hwindow); destruct pt; intros [Hinv|[Hinv|[Hinv|Hinv]]]...
    + apply (IHHreachable (DOMPath lst (DOMIndex idx)) _ ctx csp)...
      apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
    + destruct Hinv as (ctx',(wd_idx',(Hsubwindow,Hrender)))...
      destruct Hrender as (H2,(H3,(H4,(H5,(H6,H7)))));
      destruct (rp_content rp); try contradiction; destruct H7 as (H7,H8);
      destruct dm_lv_pt...
      * exfalso.
        destruct c; try contradiction; destruct H8 as (H8,H9); rewrite H9 in *...
        unfold is_script_at_page_index in Hscript_at_index...
        destruct (map_render_static_element_is_form_or_none (html_body celt_html) idx) as [H'|(mth,(act,H'))]; rewrite H' in Hscript_at_index...
      * destruct (html_body (dc_html (wd_document ctx')).[dm_pt_index]); try contradiction; destruct H8 as (H8,(H9,H10)); rewrite H10 in *...
        destruct (Nat.eq_dec dm_pt_index idx) as [Heq|Hnq]...
        -- unfold is_script_at_page_index in Hscript_at_index; unfold Array.store in Hscript_at_index; unfold Array.select in Hscript_at_index...
           rewrite Nat.eqb_refl in Hscript_at_index; destruct c; try contradiction...
           destruct H9 as (H9,H10); rewrite Hheader in H10; rewrite Horigin in H10...
        -- apply (IHHreachable (DOMPath lst (DOMIndex idx)) _ ctx')...
           apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
           apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript_at_index)...
    + destruct Hinv as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hsubwindow,(Hframe,Heq))))))))...
      destruct (Nat.eq_dec frm_idx' idx) as [Heq|Hnq]...
      * exfalso.
        unfold is_script_at_page_index in Hscript_at_index; unfold Array.store in Hscript_at_index; unfold Array.select in Hscript_at_index...
        rewrite Nat.eqb_refl in Hscript_at_index...
      * apply (IHHreachable (DOMPath lst (DOMIndex idx)) _ ctx')...
        apply (Script_in_dom_pt _ _ _ _ _ idx lst)...
        apply (same_script_at_page_index _ _ _ _ _ Hnq Hscript_at_index)...
    + exfalso.
      destruct Hinv as (ctx'',(ctx',(frm_idx',(frm',(frm_html',(frm_wd_idx',(Hcontent,(Hframe,Hrender))))))))...
      destruct Hrender as (H2,(H3,(H4,(H5,(H6,H7)))));
      rewrite Hcontent in H7; destruct H7 as (H7,H8);
      destruct (html_body (dc_html (wd_document ctx'')).[frm_idx']); try contradiction; destruct H8 as (H8,((H9,H10),H11))...
      unfold is_frame_window_at_page_index in Hframe; rewrite H10 in *; destruct Hframe as (Hframe,Heq)...
      unfold is_script_at_page_index in Hscript_at_index...
      destruct (map_render_static_element_is_form_or_none (html_body frm_html') idx) as [H'|(mth,(act,H'))]; rewrite H' in Hscript_at_index...
  - intros pt sc_ ctx csp origin Hscript Hheader Horigin...
    pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (is_script_update_initiator _ st _ _ _ _ _ _ H5 Hscript) as (ctx',(Hscript_,(Hheader_,Horigin_)));
    pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (is_script_update_html _ st_ _ _ _ _ _ _ _ H4 Hscript_) as (ctx'',(Hscript__,(Hheader__,Horigin__)))...
    rewrite Hheader_ in Hheader; rewrite Hheader__ in Hheader;
    rewrite Horigin_ in Horigin; rewrite Horigin__ in Horigin;
    apply (IHHreachable _ _ _ _ _ Hscript__ Hheader Horigin)...
  - intros pt sc_ ctx csp origin Hscript Hheader Horigin...
    pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
    destruct (is_script_update_initiator _ st _ _ _ _ _ _ H5 Hscript) as (ctx',(Hscript_,(Hheader_,Horigin_)));
    pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (is_script_update_html _ st_ _ _ _ _ _ _ _ H3 Hscript_) as (ctx'',(Hscript__,(Hheader__,Horigin__)))...
    rewrite Hheader_ in Hheader; rewrite Hheader__ in Hheader;
    rewrite Horigin_ in Horigin; rewrite Horigin__ in Horigin;
    apply (IHHreachable _ _ _ _ _ Hscript__ Hheader Horigin)...
  - intros pt sc_ ctx csp origin Hscript Hheader Horigin...
    pose (st := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
    destruct (is_script_update_domain _ st _ _ _ _ _ _ _ H2 Hscript) as (ctx',(Hscript_,(Hheader_,Horigin_)));
    rewrite Hheader_ in Hheader; rewrite Horigin_ in Horigin;
    apply (IHHreachable _ _ _ _ _ Hscript_ Hheader Horigin)...
Qed.


Theorem fix_CSPInvariant : forall gb evs st,
    c_origin_wide_csp (config gb) = true ->
    c_domain_relaxation (config gb) = false ->
    CSPInvariant gb evs st.
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st Hwide Hdomain pt sc ctx pt_u src origin tctx csp_tt _evs Hreachable_ Hscript Heq Hheader Horigin...
  inversion Hreachable_; rename H3 into Hreachable; rename H5 into Hscript_; clear H7 H9...
  specialize (origin_wide_implies_CSP_subsume_window_context _ _ _ Hwide Hdomain Hreachable) as Hcsp.
  inversion Hscript_; rename H into Hwindow; rename H1 into His_script_at...
  pose (st := {{st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg}});
  destruct (is_script_update_initiator _ st _ _ _ _ _ _ H11 Hscript) as (ctx',(Hscript__,_));
  pose (st_ := {{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}});
  destruct (is_script_update_html _ st_ _ _ _ _ _ _ _ H10 Hscript__) as (ctx'',(Hscript___,_));
  destruct (eq_is_script_in_dom_path _ _ _ _ _ _ _ Hscript_ Hscript___); clear st st_ Hscript__ Hscript___...
  inversion H6; inversion H; injection H0; clear H H0 H6; intros...
  inversion H11; injection H; clear H; intros...
  inversion H10; injection H; clear H; intros...
  rename H0 into Hsame_origin.
  assert ((wd_document_domain st_wd) = None) as H by apply (no_relaxation_implies_empty_top_domain _ _ _ Hdomain Hreachable);
  unfold is_same_origin_window_domain in Hsame_origin; rewrite H in Hsame_origin; destruct (wd_document_domain ctx''); try contradiction;
  clear Hdomain H; destruct Hsame_origin as (Hsame_origin1,Hsame_origin2)...
  specialize (Hcsp _ _ Hwindow Hsame_origin1 Hsame_origin2).
  destruct (CSP_subsume_src_match _ _ src csp_tt origin (script_src sc) Hcsp Hheader) as (x, (x0, (H, H0))); apply H0; apply (script_match_csp_src _ _ _ _ _ _ x x0 origin Hreachable Hscript_ H)...
Qed.


InlineRelation is_secure_context             With Depth 1.
InlineRelation is_not_secure_context         With Depth 1.
InlineRelation is_emitter_window_context     With Depth 1.
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
Extract Query CSPQuery Using Lemma extracted_lemma_cspquery.
