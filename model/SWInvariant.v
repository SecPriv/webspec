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


Definition SWInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall corr rq_idx rp_idx rp em,
    Reachable gb evs st ->
    (* Get the server response *)
    is_server_response gb rq_idx rp ->
    (* Get the response that was rendered *)
    in_history (st_fetch_engine st) corr (em, rq_idx, rp_idx) ->
    (* The CSP of the rendered response is equal to the server one *)
    rp_hd_csp (rp_headers rp) = rp_hd_csp (rp_headers ((responses gb).[rp_idx])).


(* Fix the issue by disallowing scripts to update the cache with:
   c_worker_allow_synthetic_responses (config gb) = false ->
   c_script_update_cache (config gb) = false ->
*)
Inductive SWQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall corr rq_idx rp_idx rp em,
    Reachable gb evs st ->
    c_worker_allow_synthetic_responses (config gb) = false ->
    (* Get the server response *)
    is_server_response gb rq_idx rp ->
    (* Get the response that was rendered *)
    in_history (st_fetch_engine st) corr (em, rq_idx, rp_idx) ->
    (* The CSP of the rendered response is equal to the server one *)
    rp_hd_csp (rp_headers rp) <> rp_hd_csp (rp_headers ((responses gb).[rp_idx])) ->
    SWQuery gb evs st.


Theorem SWQuery_invalidate_SWInvariant :
  forall gb evs st (x:SWQuery gb evs st),
    SWInvariant gb evs st -> False.
Proof.
  intros.
  unfold SWInvariant in H.
  destruct x.
  specialize (H  corr rq_idx rp_idx rp em H0 H2 H3).
  congruence.
Qed.


Lemma uniqueness_of_indexes :
  forall T array N M v,
    @distinct T array ->
    array.[ N ] = v ->
    array.[ M ] = v ->
    M = N.
Proof.
  intros.
  unfold distinct, pairwise in H.
  remember (Nat.eqb M N) as EQ.
  destruct (EQ).
  - apply eq_sym in HeqEQ. apply PeanoNat.Nat.eqb_eq in HeqEQ. auto.
  - destruct (PeanoNat.Nat.eq_dec M N). tauto.
    specialize (H M N n). subst. congruence.
Qed.


Lemma reachable_implies_distinct_response :
  forall gb evs st, Reachable gb evs st -> @distinct Response (responses gb).
Proof.
  intros gb evs st HR.
  induction HR; tauto.
Qed.

Lemma reachable_implies_distinct_request :
  forall gb evs st, Reachable gb evs st -> @distinct Request (requests gb).
Proof.
  intros gb evs st HR.
  induction HR; tauto.
Qed.


Lemma cache_or_ft_response_implies_server_response :
  forall gb
    (HS: c_worker_allow_synthetic_responses (config gb) = false),
         c_script_update_cache (config gb) = false ->
    forall evs st rq rq_idx rp rp_idx,
      Reachable gb evs st ->
      rq = (requests gb.[rq_idx]) ->
      rp = (responses gb.[rp_idx]) ->
      not (is_local_scheme (rq_url rq)) ->
      not (is_local_scheme (rp_url rp)) ->
      (
        ((wk_cache (st_service_worker st)).[rq_idx]) = Some rp_idx ->
        server_responses gb.[rq_idx] = rp_idx
      ) /\ (
        ft_request (st_fetch_engine st) = rq ->
        ft_response (st_fetch_engine st) = Some rp ->
        server_responses gb.[rq_idx] = rp_idx
      ).
Proof.
  intros.
  induction H0; try (subst; simpl in *; subst; congruence).
  - simpl. split; discriminate.
  - subst. simpl in *. firstorder. discriminate.
  - simpl in *. split. tauto.
    intros.
    assert (rp = rp0). { rewrite H10 in H13. simpl in H13. congruence. }
    assert (rp = (responses gb.[rp_idx]) ->
            rp = (responses gb.[rp_idx0]) ->
            rp_idx = rp_idx0). {
      intros.
      apply uniqueness_of_indexes with
          (T := Response) (array := responses gb) (v := rp).
      eapply reachable_implies_distinct_response with
          (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }})).
      apply H0. apply eq_sym in H14. all: firstorder.
    }
    assert (rp_idx0 = rp_idx). {
      apply eq_sym. subst. firstorder.
    }
    assert (rq_idx0 = rq_idx). {
      apply uniqueness_of_indexes with
          (T := Request) (array := requests gb) (v := rq).
      eapply reachable_implies_distinct_request with
          (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }})).
      apply H0. apply eq_sym. all: try tauto.
      rewrite H10 in H12. simpl in *.
      rewrite H6 in H12. apply H12.
    }
    apply uniqueness_of_indexes with
        (T := Response) (array := responses gb) (v := rp).
    eapply reachable_implies_distinct_response with
        (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}})).
    apply H0. apply eq_sym. firstorder.
    unfold not, is_local_scheme in H3, H4.
    rewrite <- H14 in *.
    destruct (url_protocol (rp_url rp)); firstorder;
    assert (He: rq_idx = rq_idx0) by congruence; rewrite He in *; tauto.

  - split.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx); firstorder.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx).
      -- case_eq (Nat.eqb rp_idx0 rp_idx).
         ** firstorder.
            apply PeanoNat.Nat.eqb_eq in H16, H17.
            subst. firstorder.
         ** intros. assert (rp = (responses gb.[rp_idx0])). firstorder.
             assert (rp_idx = rp_idx0). {
               apply uniqueness_of_indexes with
                   (T := Response) (array := responses gb) (v := rp).
               eapply reachable_implies_distinct_response with
                   (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg}})).
               - apply H0.
               - subst. simpl in H13. congruence.
               - apply (eq_sym H2).
             }
             apply eq_sym in H14.
             subst. congruence.
             subst. apply PeanoNat.Nat.eqb_eq in H17. subst. auto.
             subst. simpl in *.  apply PeanoNat.Nat.eqb_eq in H17. subst.

             apply uniqueness_of_indexes with (N:=rp_idx) (M:=rp_idx0) in H18.
             subst. apply (H14 H9).
             apply reachable_implies_distinct_response with
                 (evs := st_ev) (gb := gb)
                 (st := ({{st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg}})).
             apply H0. reflexivity.
      -- assert (rq_idx0 = rq_idx). {
           apply uniqueness_of_indexes with
               (T := Request) (array := requests gb) (v := rq).
           eapply reachable_implies_distinct_request with
               (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg}})).
           apply H0. apply (eq_sym H1).
           rewrite H11 in H12. rewrite H7 in H12.  apply H12.
         }
         intros. subst.
         assert (rq_idx = rq_idx) by reflexivity.
         apply PeanoNat.Nat.eqb_eq in H1. congruence.
  - split.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx).
      -- case_eq (Nat.eqb rp_idx0 rp_idx).
         ** intros. subst. rewrite HS in H5.
            apply PeanoNat.Nat.eqb_eq in H10,H11. subst. tauto.
         ** intros. subst. rewrite HS in H5. simpl in *.
            apply PeanoNat.Nat.eqb_eq in H11. subst.
            assert (rp_idx0 = rp_idx). {
              unfold store,select in *.
              case_eq (Nat.eqb rq_idx rq_idx).
              - intros. rewrite H1 in H7. congruence.
              - intros. assert (Hr: rq_idx = rq_idx) by reflexivity.
                apply PeanoNat.Nat.eqb_eq in Hr. congruence.
            }
            subst. tauto.
      -- intros.
         assert (((wk_cache st_wk.[rq_idx0]<-Some rp_idx0).[rq_idx])
                 = (wk_cache st_wk.[rq_idx])). {
           unfold select, store.
           rewrite HS in H5.
           rewrite H10. tauto.
         }
         simpl in *. subst. simpl in H7. rewrite H11 in H7. apply (H8 H7).
    * intros. destruct IHReachable. firstorder.
Qed.


Theorem script_update_cache_disabled_implies_no_tampering :
  forall gb,
    c_worker_allow_synthetic_responses (config gb) = false ->
    c_script_update_cache (config gb) = false ->
    forall evs st corr rq_idx rp_idx rp em,
      Reachable gb evs st ->
      is_server_response gb rq_idx rp ->

      in_history (st_fetch_engine st) corr (em, rq_idx, rp_idx) ->

      ((responses gb).[rp_idx]) = rp.
Proof.
  intros.
  unfold in_history in *.
  unfold is_server_response in H2.
  induction H1; try (simpl in *; subst; tauto).
  - simpl in H3. discriminate.
  - rewrite H9 in H3. simpl in *.
    unfold select,store in *.
    destruct (Nat.eqb corr0 corr).
    -- assert (Heq1: rq_idx0 = rq_idx) by congruence.
       rewrite Heq1 in *.
       assert (Heq2: rp_idx0 = rp_idx) by congruence.
       rewrite Heq2 in *.
       unfold is_valid_fetch_response in H6.
       destruct H7, H11, H12.
       rewrite H5 in H12.
       unfold not, is_local_scheme in H2.
       rewrite H12 in H8.
       destruct (url_protocol (rq_url (requests gb rq_idx)));
       (subst; destruct H2; unfold is_server_response in H8; destruct H8; subst;
         apply (eq_sym H9)) || ( subst; destruct H2; firstorder).
    -- apply IHReachable. firstorder.
  - rewrite H10 in H3. simpl in *.
    unfold select,store in *.
    destruct (Nat.eqb (ft_correlator st_ft) corr).
    -- assert (Heq1: rq_idx0 = rq_idx) by congruence.
       rewrite Heq1 in *.
       assert (Heq2: rp_idx0 = rp_idx) by congruence.
       rewrite Heq2 in *.
       assert (forall  evs st rq rq_idx rp rp_idx,
                  Reachable gb evs st ->
                  rq = (requests gb.[rq_idx]) ->
                  rp = (responses gb.[rp_idx]) ->
                   not (is_local_scheme (rq_url rq)) ->
                   not (is_local_scheme (rp_url rp)) ->

                  ((wk_cache (st_service_worker st)).[rq_idx]) = Some rp_idx ->
                  server_responses gb.[rq_idx] = rp_idx). {
         apply cache_or_ft_response_implies_server_response.
         apply H. apply H0.
         }
       assert (rp_idx = server_responses gb rq_idx). {
         apply eq_sym; eapply H11.
         apply H1. exists. exists. rewrite H6 in H5. apply H5.
         unfold is_valid_fetch_response in H9. destruct H9,H12,H13.
         unfold select. rewrite H13. apply H5. apply H8.
       }
       destruct H2. rewrite <- H12 in H13. apply H13.
    -- apply IHReachable. firstorder.
Qed.


Theorem fix_SWInvariant :
  forall gb evs st,
    c_worker_allow_synthetic_responses (config gb) = false ->
    c_script_update_cache (config gb) = false ->
    SWInvariant gb evs st.
Proof.
  unfold SWInvariant.
  intros.
  assert (responses gb.[rp_idx] = rp).
  eapply script_update_cache_disabled_implies_no_tampering; try tauto.
  apply H1. apply H2. apply H3. subst. tauto.
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
InlineRelation update_html_req_initiator     With Depth 0.
InlineRelation is_valid_setcookie_from_ctx   With Depth 0.
InlineRelation in_redirect_history           With Depth 2.
InlineRelation Scriptstate                   With Depth 5.

Set Array Size 5.
Require Import BrowserStates.
Extract Query SWQuery Using Lemma script_state_secure_is_reachable.
