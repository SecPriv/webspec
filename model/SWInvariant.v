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
From Hammer Require Import Tactics.


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
  destruct (EQ); hauto b:on.
Qed.


Lemma reachable_implies_distinct_response :
  forall gb evs st, Reachable gb evs st -> @distinct Response (responses gb).
Proof.
  intros gb evs st HR.
  induction HR; try(sfirstorder).
Qed.

Lemma reachable_implies_distinct_request :
  forall gb evs st, Reachable gb evs st -> @distinct Request (requests gb).
Proof.
  intros gb evs st HR.
  induction HR; try(sfirstorder).
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
  induction H0; try(sfirstorder).
  - qauto unfold: select,const.
  - simpl in *. split. sfirstorder.
    intros.
    assert (rp = rp0). fcrush.
    assert (rp = (responses gb.[rp_idx]) ->
            rp = (responses gb.[rp_idx0]) ->
            rp_idx = rp_idx0). {
      intros.
      apply uniqueness_of_indexes with
          (T := Response) (array := responses gb) (v := rp).
      eapply reachable_implies_distinct_response with
          (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }})).
      apply H0. apply eq_sym in H14. all: sfirstorder.
    }
    assert (rp_idx0 = rp_idx). {
      apply eq_sym. sfirstorder.
    }
    assert (rq_idx0 = rq_idx). {
      apply uniqueness_of_indexes with
          (T := Request) (array := requests gb) (v := rq).
      eapply reachable_implies_distinct_request with
          (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }})).
      apply H0. apply eq_sym. all: sfirstorder.
    }
    apply uniqueness_of_indexes with
        (T := Response) (array := responses gb) (v := rp).
    eapply reachable_implies_distinct_response with
        (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg}})).
    apply H0. apply eq_sym. sfirstorder.
    unfold not, is_local_scheme in H3, H4.
    rewrite <- H14 in *.
    destruct (url_protocol (rp_url rp)); try sfirstorder.

  - split.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx); sfirstorder.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx).
      -- case_eq (Nat.eqb rp_idx0 rp_idx).
         ** hauto b:on.
         ** intros. assert (rp = (responses gb.[rp_idx0])). fcrush.
             assert (rp_idx = rp_idx0). {
               apply uniqueness_of_indexes with
                   (T := Response) (array := responses gb) (v := rp).
               eapply reachable_implies_distinct_response with
                   (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg}})).
               all: fcrush.
             }
             apply eq_sym in H14.
             all: hauto b:on.
      -- assert (rq_idx0 = rq_idx). {
           apply uniqueness_of_indexes with
               (T := Request) (array := requests gb) (v := rq).
           eapply reachable_implies_distinct_request with
               (gb := gb) (st := ({{st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg}})).
           all: fcrush.
         }
         hauto b:on.
  - split.
    * intros. destruct IHReachable.
      case_eq (Nat.eqb rq_idx0 rq_idx).
      -- case_eq (Nat.eqb rp_idx0 rp_idx).
         ** intros. subst. rewrite HS in H5. hauto b:on.
         ** intros. subst. rewrite HS in H5. simpl in *.
            hauto depth: 2 lq: on exh: on use: PeanoNat.Nat.eqb_eq unfold: Index, select, store.
      -- intros.
         assert (((wk_cache st_wk.[rq_idx0]<-Some rp_idx0).[rq_idx])
                 = (wk_cache st_wk.[rq_idx])). {
           unfold select, store.
           rewrite HS in H5.
           hauto lq:on.
         }
         hauto.
    * intros. destruct IHReachable.
      sfirstorder.
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
  induction H1; try(sfirstorder).
  - fcrush.
  - rewrite H9 in H3. simpl in *.
    unfold select,store in *.
    destruct (Nat.eqb corr0 corr).
    -- assert (Heq1: rq_idx0 = rq_idx). sfirstorder.
       rewrite Heq1 in *.
       assert (Heq2: rp_idx0 = rp_idx). sfirstorder.
       rewrite Heq2 in *.
       unfold is_valid_fetch_response in H6.
       destruct H7, H11, H12.
       rewrite H5 in H12.
       unfold not, is_local_scheme in H2.
       rewrite H12 in H8.
       destruct (url_protocol (rq_url (requests gb rq_idx))); sfirstorder || hauto b:on.
    -- apply IHReachable. sfirstorder.
  - rewrite H10 in H3. simpl in *.
    unfold select,store in *.
    destruct (Nat.eqb (ft_correlator st_ft) corr).
    -- assert (Heq1: rq_idx0 = rq_idx). sfirstorder.
       rewrite Heq1 in *.
       assert (Heq2: rp_idx0 = rp_idx). sfirstorder.
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
         apply eq_sym; eapply H11; sfirstorder || hauto lq:on.
       }
       sfirstorder.
    -- apply IHReachable. sfirstorder.
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
  eapply script_update_cache_disabled_implies_no_tampering; hauto q:on.
  sfirstorder.
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
Require Import BrowserStates.
Extract Query SWQuery Using Lemma script_state_is_reachable.
