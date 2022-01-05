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

Require Import Arith.PeanoNat.


Lemma array_distinct_inversion :
 forall A (array: array A), Array.distinct array ->
   forall idx1 idx2, (array.[idx1]) = (array.[idx2]) -> idx1 = idx2.
Proof with subst; simpl in *; auto; try congruence.
  intros A array Hdistinct idx1 idx2 H.
  unfold distinct in Hdistinct.
  unfold pairwise in Hdistinct.
  destruct (Nat.eq_dec idx1 idx2) as [Heq|Hnq]...
  exfalso; apply (Hdistinct idx1 idx2 Hnq)...
Qed.


Definition eq_dec_NestedDOMPath (pt1 pt2 : NestedDOMPath) : { pt1 = pt2 } + { pt1 <> pt2 } :=
match pt1, pt2 with
| DOMPath dm_lvs1 dm_lv_pt1, DOMPath dm_lvs2 dm_lv_pt2 =>
  match list_eq_dec Nat.eq_dec dm_lvs1 dm_lvs2 with
  | left Hlist =>
    eq_rec_r
      (fun dm_lvs3 : list nat =>
       {DOMPath dm_lvs3 dm_lv_pt1 = DOMPath dm_lvs2 dm_lv_pt2} +
       {DOMPath dm_lvs3 dm_lv_pt1 <> DOMPath dm_lvs2 dm_lv_pt2})
      match dm_lv_pt1, dm_lv_pt2 with
      | DOMTopLevel, DOMTopLevel => left eq_refl
      | DOMTopLevel, DOMIndex n2 =>
        right
          (fun H : DOMPath dm_lvs2 DOMTopLevel = DOMPath dm_lvs2 (DOMIndex n2) =>
           eq_ind (DOMPath dm_lvs2 DOMTopLevel)
             (fun e : NestedDOMPath =>
              match e with
              | DOMPath _ DOMTopLevel => True
              | DOMPath _ (DOMIndex _) => False
              end) I (DOMPath dm_lvs2 (DOMIndex n2)) H)
      | DOMIndex n1, DOMTopLevel =>
        right
          (fun H : DOMPath dm_lvs2 (DOMIndex n1) = DOMPath dm_lvs2 DOMTopLevel =>
           eq_ind (DOMPath dm_lvs2 (DOMIndex n1))
             (fun e : NestedDOMPath =>
              match e with
              | DOMPath _ DOMTopLevel => False
              | DOMPath _ (DOMIndex _) => True
              end) I (DOMPath dm_lvs2 DOMTopLevel) H)
      | DOMIndex n1, DOMIndex n2 =>
        match Nat.eq_dec n1 n2 with
        | left Hnat =>
          left
            (eq_ind_r
               (fun n3 : nat => DOMPath dm_lvs2 (DOMIndex n3) = DOMPath dm_lvs2 (DOMIndex n2))
               eq_refl Hnat)
        | right Hnat =>
          right
            (fun H : DOMPath dm_lvs2 (DOMIndex n1) = DOMPath dm_lvs2 (DOMIndex n2) =>
             Hnat
               (f_equal
                 (fun e : NestedDOMPath =>
                  match e with
                  | DOMPath _ DOMTopLevel => n1
                  | DOMPath _ (DOMIndex dm_pt_index) => dm_pt_index
                  end) H))
        end
      end Hlist
  | right Hlist =>
    right
      (fun H : DOMPath dm_lvs1 dm_lv_pt1 = DOMPath dm_lvs2 dm_lv_pt2 =>
       Hlist (f_equal (fun e : NestedDOMPath => match e with DOMPath dm_lvs _ => dm_lvs end) H))
  end
end.


Lemma not_equal_diverge :
  forall (d1 d2: NestedDOMPath), (d1 <> d2) ->
  exists l,
        ((exists s1 s2, s1 <> s2 /\ d1 = DOMPath l s1 /\ d2 = DOMPath l s2)
      \/ (exists l2 s1 s2, l2 <> [] /\ d1 = DOMPath l s1 /\ d2 = DOMPath (l ++ l2) s2)
      \/ (exists l1 s1 s2, l1 <> [] /\ d1 = DOMPath (l ++ l1) s1 /\ d2 = DOMPath l s2)
      \/ (exists l1 l2 s1 s2 n m, n <> m /\ d1 = DOMPath (l ++ (n :: l1)) s1 /\ d2 = DOMPath (l ++ (m :: l2)) s2)).
Proof with subst; simpl in *; auto; try congruence.
  intros (ls1,pt1); induction ls1 as [ | n1 ls1 ];
  intros (ls2,pt2) Hnq; destruct ls2 as [ | n2 ls2 ].
  - destruct pt1 as [ | pt1 ]; destruct pt2 as [ | pt2 ].
    + congruence.
    + exists []; left; exists DOMTopLevel; exists (DOMIndex pt2); firstorder...
    + exists []; left; exists (DOMIndex pt1); exists DOMTopLevel; firstorder...
    + exists []; left; exists (DOMIndex pt1); exists (DOMIndex pt2); firstorder...
  - exists []; right; left; exists (n2 :: ls2); exists pt1; exists pt2; firstorder...
  - exists []; right; right; left; exists (n1 :: ls1); exists pt1; exists pt2; firstorder...
  - destruct (eq_dec_NestedDOMPath (DOMPath ls1 pt1) (DOMPath ls2 pt2)) as [Hd|Hd];
    destruct (Nat.eq_dec n1 n2) as [Hn|Hn]...
    + injection Hd; clear Hd; intros; exists []; right; right; right;
      exists ls2; exists ls2; exists pt2; exists pt2; exists n1; exists n2...
    + specialize (IHls1 (DOMPath ls2 pt2) Hd).
      destruct IHls1 as (ls,[(d1,(d2,(Hs,(H1,H2))))|[(ls',(d1,(d2,(Hs,(H1,H2)))))|[(ls',(d1,(d2,(Hs,(H1,H2)))))|(l1,(l2,(d1,(d2,(n,(m,(Hs,(H1,H2))))))))]]]).
      * injection H1; injection H2; clear H1; clear H2; intros;
        exists (n2 :: ls); left; exists d1; exists d2...
      * injection H1; injection H2; clear H1; clear H2; intros;
        exists (n2 :: ls); right; left; exists ls'; exists d1; exists d2...
      * injection H1; injection H2; clear H1; clear H2; intros;
        exists (n2 :: ls); right; right; left; exists ls'; exists d1; exists d2...
      * injection H1; injection H2; clear H1; clear H2; intros;
        exists (n2 :: ls); right; right; right; exists l1; exists l2; exists d1; exists d2; exists n; exists m...
    + exists []; right; right; right; exists ls1; exists ls2; exists pt1; exists pt2; exists n1; exists n2...
Qed.


Lemma induction_pair_NestedDOMPath :
  forall (P: NestedDOMPath -> NestedDOMPath -> Prop),
  (forall d1 d2, P (DOMPath [] d1) (DOMPath [] d2)) ->
  (forall n1 ls1 d1 d2, P (DOMPath (n1 :: ls1) d1) (DOMPath [] d2)) ->
  (forall n2 ls2 d1 d2, P (DOMPath [] d1) (DOMPath (n2 :: ls2) d2)) ->
  (forall n1 n2 ls1 ls2 d1 d2, n1 <> n2 -> P (DOMPath (n1 :: ls1) d1) (DOMPath (n2 :: ls2) d2)) ->
  (forall a ls1 ls2 d1 d2, P (DOMPath ls1 d1) (DOMPath ls2 d2) -> P (DOMPath (a :: ls1) d1) (DOMPath (a :: ls2) d2)) ->
  forall pt1 pt2, P pt1 pt2.
Proof with subst; simpl in *; auto; try congruence.
  intros P Q1 Q2 Q3 Q4 Qrec pt1 pt2; generalize P Q1 Q2 Q3 Q4 Qrec; clear P Q1 Q2 Q3 Q4 Qrec;
  destruct (eq_dec_NestedDOMPath pt1 pt2) as [H|Hnq]; [ subst; destruct pt2 as (ls,ds) | ].
  - intros P Q1 Q2 Q3 Q4; induction ls; subst; auto.
  - destruct (not_equal_diverge _ _ Hnq) as (ls,[(d1,(d2,(Hs,(H1,H2))))|[([ |x ls'],(d1,(d2,(Hs,(H1,H2)))))|[([ |x ls'],(d1,(d2,(Hs,(H1,H2)))))|(l1,(l2,(d1,(d2,(n,(m,(Hs,(H1,H2))))))))]]]);
    generalize Hnq H1 H2; generalize pt1 pt2; clear Hnq H1 H2 pt1 pt2; induction ls; intros pt1 pt2 Hnq H1 H2 P Q1 Q2 Q3 Q4 Qrec; subst; simpl in *;
    auto; apply Qrec; apply IHls; auto; congruence.
Qed.


Lemma render_static_element_is_form_or_none :
  forall celt,
    render_static_element celt = None \/
    exists frm_mth frm_act, render_static_element celt = Some (DOMElementForm {| form_method := frm_mth; form_action := frm_act |}).
Proof with subst; simpl in *; auto; try congruence.
  intros celt.
  case_eq (render_static_element celt); intros; [ right| ]...
  unfold render_static_element in H; destruct celt; [destruct h| ]...
  injection H; intros; exists html_form_method; exists html_form_action...
Qed.


Lemma map_render_static_element_is_form_or_none :
  forall array idx,
    (Array.map render_static_element array).[idx] = None \/
    exists frm_mth frm_act, (Array.map render_static_element array).[idx] = Some (DOMElementForm {| form_method := frm_mth; form_action := frm_act |}).
Proof with subst; simpl in *; auto; try congruence.
  intros array idx; unfold Array.map; unfold Array.select;
  apply render_static_element_is_form_or_none.
Qed.


Lemma same_frame_window_at_page_index :
  forall gb pg frm frm_html frm_wd idx idx' elt,
    idx' <> idx ->
    is_frame_window_at_page_index gb
       {|
         dm_nonce := dm_nonce pg;
         dm_head  := dm_head pg;
         dm_body  := dm_body pg.[idx']<- elt
       |} idx frm frm_html frm_wd ->
    is_frame_window_at_page_index gb pg idx frm frm_html frm_wd.
Proof with subst; simpl in *; auto; try congruence.
  intros gb pg frm frm_html frm_wd idx idx' elt Hnq Hframe.
  unfold is_frame_window_at_page_index in *...
  unfold is_frame_at_page_index in *...
  unfold Array.select in *; unfold Array.store in *.
  destruct (Nat.eqb_neq idx' idx) as (_,Heqb); specialize (Heqb Hnq).
  rewrite Heqb in Hframe...
Qed.


Lemma content_frame_window_at_page_index :
  forall gb pg frm frm_html frm_wd idx elt,
    is_frame_window_at_page_index gb
       {|
         dm_nonce := dm_nonce pg;
         dm_head  := dm_head pg;
         dm_body  := dm_body pg.[idx]<- elt
       |} idx frm frm_html frm_wd ->
    exists url, elt = Some (DOMElementResource url (ContentElementFrame frm frm_html)) /\
    (windows gb.[frame_window frm]) = frm_wd.
Proof with subst; simpl in *; auto; try congruence.
  intros gb pg frm frm_html frm_wd idx elt H;
  unfold is_frame_window_at_page_index in H; unfold is_frame_at_page_index in H;
  unfold Array.store in H; unfold Array.select in H; destruct H...
  rewrite Nat.eqb_refl in H; destruct elt; try contradiction;
  destruct d; try contradiction; destruct pg_sr_ce; try contradiction;
  destruct H; exists pg_sr_src...
Qed.


Lemma same_script_at_page_index :
  forall pg sc idx idx' elt,
    idx' <> idx ->
    is_script_at_page_index {|
         dm_nonce := dm_nonce pg;
         dm_head  := dm_head pg;
         dm_body  := dm_body pg.[idx']<- elt
       |} idx sc ->
    is_script_at_page_index pg idx sc.
Proof with subst; simpl in *; auto; try congruence.
  intros pg sc idx idx' elt Hnq Hscript.
  unfold is_script_at_page_index in *...
  unfold Array.select in *; unfold Array.store in *.
  destruct (Nat.eqb_neq idx' idx) as (_,Heqb); specialize (Heqb Hnq).
  rewrite Heqb in Hscript...
Qed.


Lemma content_script_at_page_index :
  forall pg sc idx elt,
    is_script_at_page_index {|
         dm_nonce := dm_nonce pg;
         dm_head  := dm_head pg;
         dm_body  := dm_body pg.[idx]<- elt
       |} idx sc ->
    exists url, elt = Some (DOMElementResource url (ContentElementScript sc)).
Proof with subst; simpl in *; auto; try congruence.
  intros pg sc idx elt H;
  unfold is_script_at_page_index in H;
  unfold Array.select in H; unfold Array.store in H...
  rewrite Nat.eqb_refl in H; destruct elt; try contradiction;
  destruct d; try contradiction; destruct pg_sr_ce; try contradiction;
  exists pg_sr_src...
Qed.


Lemma eq_window_ctx_of_dom_path :
  forall gb wd pt ctx1 ctx2,
    window_ctx_of_dom_path_rec gb ctx1 wd pt ->
    window_ctx_of_dom_path_rec gb ctx2 wd pt ->
    ctx1 = ctx2.
Proof with subst; simpl in *; auto; try congruence.
  intros gb wd (lst,pt) ctx1 ctx2 Hwindow1 Hwindow2.
  induction Hwindow1; inversion Hwindow2...
  injection H1; clear H1; intros; firstorder...
  unfold is_frame_at_page_index in *; firstorder...
  destruct (dm_body (dc_dom (wd_document wd)).[frm_idx0]); firstorder;
  destruct d; try (exfalso; assumption);
  destruct pg_sr_ce; try (exfalso; assumption); firstorder...
Qed.


Lemma eq_is_script_in_dom_path :
  forall gb pt wd sc1 ctx1 sc2 ctx2,
    is_script_in_dom_path gb wd pt sc1 ctx1 ->
    is_script_in_dom_path gb wd pt sc2 ctx2 ->
    sc1 = sc2 /\ ctx1 = ctx2.
Proof with subst; simpl in *; auto; try congruence.
  intros gb pt wd sc1 ctx1 sc2 ctx2 Hscript1 Hscript2;
  destruct Hscript1 as (idx1,lst1,Hwindow1,Heq1,Hscript1);
  destruct Hscript2 as (idx2,lst2,Hwindow2,Heq2,Hscript2); subst; injection Heq2; clear Heq2; intros...
  rewrite (eq_window_ctx_of_dom_path _ _ _ _ _ Hwindow1 Hwindow2) in *;
  unfold is_script_at_page_index in *;
  destruct (dm_body (dc_dom (wd_document ctx2)).[idx2]); try contradiction;
  destruct d; try contradiction; destruct pg_sr_ce; try contradiction...
Qed.


Lemma update_window_on_response_fetch_engine :
  forall gb st pt_rp rp wd,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp pt_rp (st_window st) wd ->
    ft_response (st_fetch_engine st) = Some rp.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st (ls,pt); generalize gb st; clear gb st; induction ls; intros gb st rp wd Hupdate.
  - inversion Hupdate; firstorder...
  - inversion Hupdate; injection H; clear H; intros...
    pose (st_ := {{(st_version st),(st_fetch_engine st),(st_service_worker st),frm_wd,(st_cookiejar st),(st_blob_store st),(st_local_storage st)}}).
    apply (IHls _ st_ rp _ H1)...
Qed.


Lemma update_window_on_response_inversion_nil_toplevel :
  forall gb st rp wd ctx ls2 d2,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp (DOMPath [] DOMTopLevel) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath ls2 d2) ->
    ls2 = [].
Proof with subst; simpl in *; auto; try congruence.
  intros gb st rp wd ctx ls2 d2 Hupdate Hwindow.
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  exfalso; firstorder...
  destruct (rp_content rp); try contradiction; destruct H6 as (H6,H7)...
  destruct c; try contradiction; destruct H7 as (H8,H9)...
  rewrite H9 in H; unfold is_frame_at_page_index in H...
  destruct (map_render_static_element_is_form_or_none (html_body celt_html) frm_idx_wd) as [Hmap|(mth,(act,Hmap))];
  rewrite Hmap in H...
Qed.


Lemma update_window_on_response_inversion_nil_index :
  forall gb st rp wd ctx idx ls2 d2,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp (DOMPath [] (DOMIndex idx)) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath (idx :: ls2) d2) ->
    ls2 = [].
Proof with subst; simpl in *; auto; try congruence.
  intros gb st rp wd ctx idx ls2 d2 Hupdate Hwindow.
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  destruct H1 as (H1,(H2,(H3,(H4,(H5,H6)))));
  destruct (rp_content rp); try contradiction; destruct H6 as (H6,H7);
  destruct (html_body (dc_html (wd_document (st_window st))).[idx]); try contradiction; destruct H7 as (H8,(H9,H10))...
  rewrite H10 in *...
  unfold update_page_element_at_idx in Hwindow...
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hwindow_frame) as (u_,(H_,H__)); injection H_; clear H_; intros...
  destruct H9 as (H9,H11); rewrite H11 in *;
  unfold build_toplevel_window in Hsubwindow;
  inversion Hsubwindow; injection H; clear H; intros...
  exfalso.
  unfold is_frame_window_at_page_index in H0; unfold is_frame_at_page_index in H0; destruct H0...
  destruct (map_render_static_element_is_form_or_none (html_body frm_html_) frm_idx) as [Hmap|(mth,(act,Hmap))];
  rewrite Hmap in H...
Qed.


Lemma update_window_on_response_inversion_cons :
  forall gb st rp wd ctx frm_idx ls1 d1 ls2 d2,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp (DOMPath (frm_idx :: ls1) d1) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath (frm_idx :: ls2) d2) ->
    exists frm frm_html wd_idx,
      wd = (update_page_element_at_idx
             (st_version st) (st_window st) (rp_url rp) frm_idx
             (ContentElementFrame {| frame_src := frame_src frm; frame_window := wd_idx |} frm_html))
      /\ window_ctx_of_dom_path_rec gb ctx (windows gb wd_idx) (DOMPath ls2 d2)
      /\ update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp (DOMPath ls1 d1) (windows gb.[frame_window frm]) (windows gb.[wd_idx])
      /\ is_frame_at_page_index (dc_dom (wd_document (st_window st))) frm_idx frm frm_html.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st rp wd ctx frm_idx ls1 d1 ls2 d2 Hupdate Hwindow.
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hwindow_frame) as (u_,(H_,H__)); injection H_; clear H_; intros; firstorder...
  exists frm; exists frm_html_; exists wd_idx...
Qed.


Lemma update_window_on_response_inversion :
  forall gb st pt_rp rp wd pt_ctx ctx,
    update_window_on_response gb (st_version st) (st_fetch_engine st) (st_blob_store st) rp pt_rp (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    let (ls_rp,ds_rp) := pt_rp in
    let (ls_ctx,ds_ctx) := pt_ctx in
    window_ctx_of_dom_path_rec gb ctx (st_window st) pt_ctx
 \/ (exists ctx' wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ render_window_dom_path_on_response gb (st_version st) (st_fetch_engine st) rp ds_rp ctx' ctx wd_idx (st_blob_store st))
 \/ (exists ctx' frm_idx frm frm_html frm_wd frm_wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ is_frame_window_at_page_index gb (dc_dom (wd_document ctx')) frm_idx frm frm_html frm_wd
       /\ ctx = update_page_element_at_idx (st_version st) ctx' (rp_url rp) frm_idx
                  (ContentElementFrame {| frame_src := frame_src frm; frame_window := frm_wd_idx |} frm_html))
 \/ (exists ctx'' ctx' frm_idx frm frm_html frm_wd_idx,
       rp_content rp = Some (ContentElementFrame frm frm_html)
       /\ is_frame_window_at_page_index gb (dc_dom (wd_document ctx')) frm_idx frm frm_html ctx
       /\ render_window_dom_path_on_response gb (st_version st) (st_fetch_engine st) rp (DOMIndex frm_idx) ctx'' ctx' frm_wd_idx (st_blob_store st)).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st pt_rp rp wd pt_ctx; generalize gb st rp wd; clear gb st rp wd;
  induction pt_rp,pt_ctx using induction_pair_NestedDOMPath; intros gb st rp wd ctx Hupdate Hwindow.
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; left; exists (st_window st); exists wd_idx; split...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; right; left; exists (st_window st); exists frm_idx; exists frm; exists frm_html; exists frm_wd; exists frm_wd_idx_; split...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - destruct d1; [ specialize (update_window_on_response_inversion_nil_toplevel _ _ _ _ _ _ _ Hupdate Hwindow) as H; congruence | ].
    destruct (Nat.eq_dec dm_pt_index n2) as [Heq|Hnq]...
    + specialize (update_window_on_response_inversion_nil_index _ _ _ _ _ _ _ _ Hupdate Hwindow) as H...
      inversion Hwindow; injection H; clear H; intros...
      inversion Hupdate; injection H; clear H; intros...
      inversion H1; injection H; clear H; intros...
      rename frm_wd into ctx.
      right; right; right; exists (st_window st); exists (windows gb.[wd_idx]); exists frm_idx; exists frm; exists frm_html; exists wd_idx; split; [ | split ]...
      destruct H3 as (H2,(H3,(H4,(H5,(H6,H7))))); destruct (rp_content rp); try contradiction; destruct H7 as (H7,H8);
      destruct (html_body (dc_html (wd_document (st_window st))).[frm_idx]); try contradiction; destruct H8 as (H8,(H9,H10));
      rewrite H10 in *...
      destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ H0) as (u_,(H_,H__)); injection H_; clear H_; intros...
    + left.
      inversion Hwindow; injection H; clear H; intros...
      inversion Hupdate; injection H; clear H; intros...
      destruct H3 as (H2,(H3,(H4,(H5,(H6,H7))))); destruct (rp_content rp); try contradiction; destruct H7 as (H7,H8);
      destruct (html_body (dc_html (wd_document (st_window st))).[dm_pt_index]); try contradiction; destruct H8 as (H8,(H9,H10));
      rewrite H10 in *...
      unfold update_page_element_at_idx in H0.
      destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ Hnq H0).
      apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm]) rest_idx dompath)...
      unfold is_frame_window_at_page_index...
  - left.
    inversion Hwindow; injection H0; clear H0; intros...
    inversion Hupdate; injection H0; clear H0; intros...
    destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ H H1).
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm])  rest_idx dompath)...
    unfold is_frame_window_at_page_index...
  - destruct (update_window_on_response_inversion_cons _ _ _ _ _ _ _ _ _ _ Hupdate Hwindow) as (frm,(frm_html,(wd_idx,(Hwd,(Hafter_subwindow,(Hupdate_subwindow,Hframe)))))).
    pose (st_ := {{(st_version st),(st_fetch_engine st),(st_service_worker st),(windows gb.[frame_window frm]),(st_cookiejar st),(st_blob_store st),(st_local_storage st)}}).
    destruct (IHpt_ctx _ st_ _ _ _ Hupdate_subwindow Hafter_subwindow) as [H|[H|[H|H]]]; [ left | right; left | right; right; left | right; right; right ]...
    + apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2)...
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(wd_idx',(Hsubwindow,Hrender))); exists ctx'; exists wd_idx'; split...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2)...
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hsubwindow,(Hsubframe,Hsubupdate))))))));
      exists ctx'; exists frm_idx'; exists frm'; exists frm_html'; exists frm_wd'; exists frm_wd_idx'; split; [ | split ]...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2)...
      unfold is_frame_window_at_page_index...
Qed.


Lemma update_window_html_from_ctx_inversion_cons :
  forall gb st cx html wd ctx frm_idx ls1 d1 ls2 d2,
    update_window_html_from_ctx gb (st_version st) cx html (DOMPath (frm_idx :: ls1) d1) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath (frm_idx :: ls2) d2) ->
    exists frm frm_html wd_idx,
      wd = (update_page_element_at_idx
             (st_version st) (st_window st) (wd_location (windows gb.[frame_window frm])) frm_idx
             (ContentElementFrame {| frame_src := frame_src frm; frame_window := wd_idx |} (dc_html (wd_document (windows gb.[wd_idx])))))
      /\ window_ctx_of_dom_path_rec gb ctx (windows gb wd_idx) (DOMPath ls2 d2)
      /\ update_window_html_from_ctx gb (st_version st) cx html (DOMPath ls1 d1) (windows gb.[frame_window frm]) (windows gb.[wd_idx])
      /\ is_frame_at_page_index (dc_dom (wd_document (st_window st))) frm_idx frm frm_html.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st cx html wd ctx frm_idx ls1 d1 ls2 d2 Hupdate Hwindow.
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hwindow_frame) as (u_,(H_,H__)); injection H_; clear H_; intros; firstorder...
  exists frm; exists frm_html; exists wd_idx...
Qed.


Lemma update_window_html_from_ctx_inversion :
  forall gb st cx pt_html html wd pt_ctx ctx,
    update_window_html_from_ctx gb (st_version st) cx html pt_html (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    let (ls_html,ds_html) := pt_html in
    let (ls_ctx,ds_ctx) := pt_ctx in
    window_ctx_of_dom_path_rec gb ctx (st_window st) pt_ctx
 \/ (exists ctx' wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ ctx = update_html_element_at_idx (st_version st) ctx' wd_idx html)
 \/ (exists ctx' frm_idx frm frm_html frm_wd frm_wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ is_frame_window_at_page_index gb (dc_dom (wd_document ctx')) frm_idx frm frm_html frm_wd
       /\ ctx = update_page_element_at_idx (st_version st) ctx' (wd_location frm_wd) frm_idx
               (ContentElementFrame {| frame_src := frame_src frm; frame_window := frm_wd_idx |}
                  (dc_html (wd_document (windows gb.[frm_wd_idx]))))).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st cx pt_html html wd pt_ctx; generalize gb st cx html wd; clear gb st cx html wd;
  induction pt_html,pt_ctx using induction_pair_NestedDOMPath; intros gb st cx html wd ctx Hupdate Hwindow.
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; left; exists (st_window st); exists pt_idx; split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; right; exists (st_window st); exists frm_idx; exists frm; exists frm_html; exists frm_wd; exists frm_wd_idx_; split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    destruct (Nat.eq_dec pt_idx frm_idx) as [Heq|Hnq]...
    + exfalso.
      destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ H0) as (u_,(H_,H__));
      destruct html; try contradiction...
    + left.
      destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ Hnq H0)...
      apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm]) rest_idx dompath)...
      unfold is_frame_window_at_page_index...
  - left.
    inversion Hwindow; injection H0; clear H0; intros...
    inversion Hupdate; injection H0; clear H0; intros...
    destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ H H1)...
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm]) rest_idx dompath)...
    unfold is_frame_window_at_page_index...
  - destruct (update_window_html_from_ctx_inversion_cons _ _ _ _ _ _ _ _ _ _ _ Hupdate Hwindow) as (frm,(frm_html,(wd_idx,(Hwd,(Hafter_subwindow,(Hupdate_subwindow,Hframe))))))...
    pose (st_ := {{(st_version st),(st_fetch_engine st),(st_service_worker st),(windows gb.[frame_window frm]),(st_cookiejar st),(st_blob_store st),(st_local_storage st)}}).
    destruct (IHpt_ctx _ st_ _ _ _ _ Hupdate_subwindow Hafter_subwindow) as [H|[H|H]]; [ left | right; left | right; right ]...
    + apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(wd_idx',(Hwindow',Hupdate')));
      exists ctx'; exists wd_idx'; split...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
      exists ctx'; exists frm_idx'; exists frm'; exists frm_html'; exists frm_wd'; exists frm_wd_idx'; split; [ | split ]...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
Qed.


Lemma update_html_req_initiator_inversion_cons :
  forall gb st init wd ctx frm_idx ls1 d1 ls2 d2,
    update_html_req_initiator gb (st_version st) init (DOMPath (frm_idx :: ls1) d1) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath (frm_idx :: ls2) d2) ->
    exists frm frm_html wd_idx,
      wd = (update_page_element_at_idx
             (st_version st) (st_window st) (wd_location (windows gb.[frame_window frm])) frm_idx
             (ContentElementFrame {| frame_src := frame_src frm; frame_window := wd_idx |} frm_html))
      /\ window_ctx_of_dom_path_rec gb ctx (windows gb wd_idx) (DOMPath ls2 d2)
      /\ update_html_req_initiator gb (st_version st) init (DOMPath ls1 d1) (windows gb.[frame_window frm]) (windows gb.[wd_idx])
      /\ is_frame_at_page_index (dc_dom (wd_document (st_window st))) frm_idx frm frm_html.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st init wd ctx frm_idx ls1 d1 ls2 d2 Hupdate Hwindow.
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hwindow_frame) as (u_,(H_,H__)); injection H_; clear H_; intros; firstorder...
  exists frm; exists frm_html_; exists wd_idx...
Qed.


Lemma update_html_req_initiator_inversion :
  forall gb st pt_init init wd pt_ctx ctx,
    update_html_req_initiator gb (st_version st) init pt_init (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    let (ls_init,ds_init) := pt_init in
    let (ls_ctx,ds_ctx) := pt_ctx in
    window_ctx_of_dom_path_rec gb ctx (st_window st) pt_ctx
 \/ (exists ctx' idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ ctx = update_initiator_at_idx ctx' idx init)
 \/ (exists ctx' frm_idx frm frm_html frm_wd frm_wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ is_frame_window_at_page_index gb (dc_dom (wd_document ctx')) frm_idx frm frm_html frm_wd
       /\ ctx = update_page_element_at_idx (st_version st) ctx' (wd_location frm_wd) frm_idx
                  (ContentElementFrame {| frame_src := frame_src frm; frame_window := frm_wd_idx |} frm_html)).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st pt_init init wd pt_ctx; generalize gb st init wd; clear gb st init wd;
  induction pt_init,pt_ctx using induction_pair_NestedDOMPath; intros gb st init wd ctx Hupdate Hwindow.
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; left; exists (st_window st); exists pt_idx; split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; right; exists (st_window st); exists frm_idx; exists frm; exists frm_html; exists frm_wd; exists frm_wd_idx_; split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - left.
    inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html frm_wd rest_idx dompath)...
  - left.
    inversion Hwindow; injection H0; clear H0; intros...
    inversion Hupdate; injection H0; clear H0; intros...
    destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ H H1)...
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm]) rest_idx dompath)...
    unfold is_frame_window_at_page_index...
  - destruct (update_html_req_initiator_inversion_cons _ _ _ _ _ _ _ _ _ _ Hupdate Hwindow) as (frm,(frm_html,(wd_idx,(Hwd,(Hafter_subwindow,(Hupdate_subwindow,Hframe))))))...
    pose (st_ := {{(st_version st),(st_fetch_engine st),(st_service_worker st),(windows gb.[frame_window frm]),(st_cookiejar st),(st_blob_store st),(st_local_storage st)}}).
    destruct (IHpt_ctx _ st_ _ _ _ Hupdate_subwindow Hafter_subwindow) as [H|[H|H]]; [ left | right; left | right; right ]...
    + apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(idx',(Hwindow',Hupdate')));
      exists ctx'; exists idx'; split...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
      exists ctx'; exists frm_idx'; exists frm'; exists frm_html'; exists frm_wd'; exists frm_wd_idx'; split; [ | split ]...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
Qed.


Lemma update_window_domain_from_ctx_inversion_cons :
  forall gb st cx domain wd ctx frm_idx ls1 d1 ls2 d2,
    update_window_domain_from_ctx gb (st_version st) cx domain (DOMPath (frm_idx :: ls1) d1) (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd (DOMPath (frm_idx :: ls2) d2) ->
    exists frm frm_html wd_idx,
      wd = (update_page_element_at_idx
             (st_version st) (st_window st) (wd_location (windows gb.[frame_window frm])) frm_idx
             (ContentElementFrame {| frame_src := frame_src frm; frame_window := wd_idx |} frm_html))
      /\ window_ctx_of_dom_path_rec gb ctx (windows gb wd_idx) (DOMPath ls2 d2)
      /\ update_window_domain_from_ctx gb (st_version st) cx domain (DOMPath ls1 d1) (windows gb.[frame_window frm]) (windows gb.[wd_idx])
      /\ is_frame_at_page_index (dc_dom (wd_document (st_window st))) frm_idx frm frm_html.
Proof with subst; simpl in *; auto; try congruence.
  intros gb st cx domain wd ctx frm_idx ls1 d1 ls2 d2 Hupdate Hwindow.
  inversion Hwindow as [ | wd_ pt_ frm_idx_wd frm_ frm_html_ frm_wd__ ls2_ ds2_ H Hwindow_frame Hsubwindow]; injection H; clear H; intros...
  inversion Hupdate as [ | pt_ wd_ wd__ frm_idx frm frm_html frm_wd frm_wd_ ls ds wd_idx H Hupdate_frame Hupdate_subwindow]; injection H; clear H; intros...
  destruct (content_frame_window_at_page_index _ _ _ _ _ _ _ Hwindow_frame) as (u_,(H_,H__)); injection H_; clear H_; intros; firstorder...
  exists frm; exists frm_html_; exists wd_idx...
Qed.


Lemma update_window_domain_from_ctx_inversion :
  forall gb st cx pt_cx domain wd pt_ctx ctx,
    update_window_domain_from_ctx gb (st_version st) cx domain pt_cx (st_window st) wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt_ctx ->
    let (ls_cx,ds_cx) := pt_cx in
    let (ls_ctx,ds_ctx) := pt_ctx in
    window_ctx_of_dom_path_rec gb ctx (st_window st) pt_ctx
 \/ (exists ctx',
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ ctx = update_document_domain ctx' domain)
 \/ (exists ctx' frm_idx frm frm_html frm_wd frm_wd_idx,
       window_ctx_of_dom_path_rec gb ctx' (st_window st) pt_ctx
       /\ is_frame_window_at_page_index gb (dc_dom (wd_document ctx')) frm_idx frm frm_html frm_wd
       /\ ctx = update_page_element_at_idx (st_version st) ctx' (wd_location frm_wd) frm_idx
                  (ContentElementFrame {| frame_src := frame_src frm; frame_window := frm_wd_idx |} frm_html)).
Proof with subst; simpl in *; auto; try congruence.
  intros gb st cx pt_cx domain wd pt_ctx; generalize gb st cx domain wd; clear gb st cx domain wd;
  induction pt_cx,pt_ctx using induction_pair_NestedDOMPath; intros gb st cx domain wd ctx Hupdate Hwindow.
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; left; exists (st_window st); split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    right; right; exists (st_window st); exists frm_idx; exists frm; exists frm_html; exists frm_wd; exists frm_wd_idx_; split; [ | split ]...
    apply (Window_ctx_pt_base _ _ _ _ dompt)...
  - left.
    inversion Hwindow; injection H; clear H; intros...
    inversion Hupdate; injection H; clear H; intros...
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html frm_wd rest_idx dompath)...
  - left.
    inversion Hwindow; injection H0; clear H0; intros...
    inversion Hupdate; injection H0; clear H0; intros...
    destruct (same_frame_window_at_page_index _ _ _ _ _ _ _ _ H H1)...
    apply (Window_ctx_pt_rec _ _ _ _ frm_idx frm frm_html (windows gb.[frame_window frm]) rest_idx dompath)...
    unfold is_frame_window_at_page_index...
  - destruct (update_window_domain_from_ctx_inversion_cons _ _ _ _ _ _ _ _ _ _ _ Hupdate Hwindow) as (frm,(frm_html,(wd_idx,(Hwd,(Hafter_subwindow,(Hupdate_subwindow,Hframe))))))...
    pose (st_ := {{(st_version st),(st_fetch_engine st),(st_service_worker st),(windows gb.[frame_window frm]),(st_cookiejar st),(st_blob_store st),(st_local_storage st)}}).
    destruct (IHpt_ctx _ st_ _ _ _ _ Hupdate_subwindow Hafter_subwindow) as [H|[H|H]]; [ left | right; left | right; right ]...
    + apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(Hwindow',Hupdate'));
      exists ctx'; split...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
    + destruct H as (ctx',(frm_idx',(frm',(frm_html',(frm_wd',(frm_wd_idx',(Hwindow',(Hframe',Hupdate'))))))));
      exists ctx'; exists frm_idx'; exists frm'; exists frm_html'; exists frm_wd'; exists frm_wd_idx'; split; [ | split ]...
      apply (Window_ctx_pt_rec _ _ _ _ a frm frm_html (windows gb.[frame_window frm]) ls2 d2);
      unfold is_frame_window_at_page_index...
Qed.


Lemma distinct_origin_csp :
  forall gb st evs,
    Reachable gb st evs ->
    distinct (Array.map fst (origin_csp gb)).
Proof.
  intros gb st evs Hreachable; induction Hreachable; auto.
Qed.


Lemma is_valid_url_request :
  forall gb evs st,
    Reachable gb evs st ->
    is_valid_url (rq_url (ft_request (st_fetch_engine st))).
Proof with subst; simpl in *; auto.
  intros gb evs st Hreachable.
  induction Hreachable; firstorder...
Qed.


Lemma is_valid_url_response :
  forall gb evs st rp,
    Reachable gb evs st ->
    (ft_response (st_fetch_engine st)) = Some rp ->
    is_valid_url (rp_url rp).
Proof with subst; simpl in *; auto; try congruence.
  intros gb evs st rp Hreachable Hresponse.
  assert (is_valid_url (rq_url (ft_request (st_fetch_engine st)))) as H
  by apply (is_valid_url_request _ _ _ Hreachable).
  induction Hreachable; firstorder...
Qed.


Lemma no_relaxation_implies_empty_top_domain :
  forall gb evs st,
    c_domain_relaxation (config gb) = false ->
    Reachable gb evs st ->
    (wd_document_domain (st_window st)) = None.
Proof with subst; simpl in *; auto.
  intros gb evs st Hdomain Hreachable.
  induction Hreachable; firstorder.
  - inversion H0; firstorder...
    destruct (rp_content rp); try (exfalso; assumption); firstorder.
    destruct lz_pt...
    + destruct c; try (exfalso; assumption); firstorder.
      rewrite H3; unfold build_toplevel_window...
    + destruct (html_body (dc_html (wd_document st_wd)).[dm_pt_index]); try (exfalso; assumption); firstorder.
      rewrite H5; unfold update_page_element_at_idx...
  - inversion H5; inversion H4...
  - inversion H5; inversion H3...
  - inversion H; congruence.
Qed.
