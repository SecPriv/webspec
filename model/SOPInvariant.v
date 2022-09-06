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

Require Import Coq.Lists.List.

Definition IsEvRequestCORSPreflight rq ev :=
  match ev with
  | EvRequest (EmitterCORSPreflight _ org_rq) _ _ => org_rq = rq
  | _ => False
  end.

Definition SOPInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall rq corr em rest,
    Reachable gb evs st ->
    evs = (EvRequest em rq corr :: rest) ->
    (* The request is a non-simple request *)
    not (is_cors_simple_request rq) ->
    (* The request is cross origin *)
    is_cross_origin_request (st_window st) rq ->
    (* There needs to be a preflight request *)
    Exists (IsEvRequestCORSPreflight rq) rest.


(* List.forall (fun x => not (IsEvRequestCORSPreflight rq x)) *)
Inductive all_list (rq: Request) : list Event -> Prop :=
| AllList_empty : forall llst,
    llst = nil ->
    all_list rq llst
| AllList_rec : forall llst  x rest,
    llst = cons x rest ->
    (match x with
     | EvRequest (EmitterCORSPreflight _ org_rq) _ _ => org_rq <> rq
     | _ => True
     end) /\ all_list rq rest ->
    all_list rq llst.

Lemma all_list_forall_preflight :
  forall rq _evs, List.Forall (fun x => not (IsEvRequestCORSPreflight rq x)) _evs
                  <-> all_list rq _evs.
Proof with unfold not; compute; try tauto.
  intros.
  induction _evs.
  - split; intros.
    induction H.
    * constructor. reflexivity.
    * apply AllList_rec with (x:=x) (rest:=l). reflexivity.
      unfold IsEvRequestCORSPreflight in H.
      split. induction x... induction evrq_em... apply IHForall.
    * constructor.
  - split; intros.
    induction H. constructor. reflexivity.
    apply AllList_rec with (x:= x) (rest:= l). reflexivity.
    unfold IsEvRequestCORSPreflight in H.
    split. induction x... induction evrq_em... apply IHForall.
    constructor 2.
    remember (a :: _evs) as evs.
    destruct H. congruence. destruct H0.
    assert (x = a) by congruence. subst.
    unfold IsEvRequestCORSPreflight. induction a... induction evrq_em...
    destruct IH_evs. remember (a :: _evs) as evs.
    destruct H. congruence. assert (rest = _evs) by congruence. subst. destruct H2.
    apply (H1 H3).
Qed.



(* Fix the issue by disabling early-html5 form methods with:
   c_earlyhtml5_form_methods (config gb) = false ->
 *)
Inductive SOPQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall rq corr em _evs,
    Reachable gb evs st ->
    evs = (EvRequest em rq corr :: _evs) ->
    not (is_cors_simple_request rq) ->
    (* The request is cross origin *)
    is_cross_origin_request (st_window st) rq ->
    (* There is no preceding preflight request *)
    all_list rq _evs ->
    match em with | EmitterForm _ _ => True | _ => False end ->
    SOPQuery gb evs st.


Theorem SOPQuery_invalidate_SOPInvariant :
  forall gb evs st (x:SOPQuery gb evs st),
    SOPInvariant gb evs st -> False.
Proof.
  intros.
  destruct x.
  unfold SOPInvariant in H.
  specialize (H rq corr em _evs H0 H1 H2 H3).
  apply all_list_forall_preflight in H4.
  apply Forall_Exists_neg in H4. congruence.
Qed.


InlineRelation all_list                      With Depth 6.
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
Extract Query SOPQuery.
