Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.

Require Import Browser.
Require Import BrowserStates.

(* script_state_is_reachable *)
Inductive LemmaQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state :     
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (map fst (origin_csp gb)) ->
    origin_csp gb.[0] = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None) ->
    script_state_constraints gb ->
    evs = (script_state_events gb) ->
    st = script_state ->
    Reachable gb evs st ->
    LemmaQuery gb evs st.

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
Extract Query LemmaQuery.


