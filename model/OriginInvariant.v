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


Definition OriginInvariant (gb: Global) (evs: list Event) (st: State) : Prop :=
  forall em rq corr _evs orghd orgsrc,
    Reachable gb evs st ->
    (* Request with origin header orgd *)
    evs = (EvRequest em rq corr :: _evs) ->
    rq_hd_origin (rq_headers rq) = Some orghd ->
    (* The source origin is equal to orghd *)
    is_request_source gb st rq (Some orgsrc) ->
    orgsrc = orghd.


(* Fix the issue by setting the origin header to null on cross origin redirects
    c_origin_header_on_cross_origin_redirect (config gb) = false ->
*)
Inductive OriginQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : forall em rq corr _evs orghd orgsrc,
    Reachable gb evs st ->
    (* POST request to origin o with origin header o *)
    evs = (EvRequest em rq corr :: _evs) ->
    rq_method rq = MethodPost /\ em <> EmitterWorker ->
    rq_hd_origin (rq_headers rq) = Some orghd ->
    origin_of_url (rq_url rq) = Some orghd ->
    (* The source origin is different to the header *)
    is_request_source gb st rq (Some orgsrc) ->
    orgsrc <> orghd ->
    OriginQuery gb evs st.


Theorem OriginQuery_invalidate_OriginInvariant :
  forall gb evs st (x:OriginQuery gb evs st),
    OriginInvariant gb evs st -> False.
Proof.
  intros.
  unfold OriginInvariant in H.
  destruct x.
  specialize (H em rq corr _evs orghd orgsrc H0 H1 H3 H5).
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
InlineRelation is_request_source             With Depth 0.
InlineRelation Scriptstate                   With Depth 5.

Set Array Size 5.
Extract Query OriginQuery.
