Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.

Require Import Browser.
Require Import BrowserStates.


Require Import Coq.Lists.List.
Import List.ListNotations.

(*  extracted_lemma_cspquery *)
Inductive LemmaQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state : 
    cspquery_state_6_constraints gb ->
    evs = cspquery_state_6_events ->
    st = cspquery_state_6 ->
    Reachable gb evs st ->
    LemmaQuery gb evs st.

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
Extract Query LemmaQuery.


