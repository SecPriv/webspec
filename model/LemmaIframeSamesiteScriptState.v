Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.

Require Import Browser.
Require Import BrowserStates.

(* iframe_samesite_script_state_is_reachable *)
Inductive LemmaQuery (gb: Global) (evs: list Event) (st: State) : Prop :=
| Query_state :     
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (Array.map fst (origin_csp gb)) ->
    (origin_csp gb.[0]) = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None) ->
    c_origin_wide_csp (config gb) = false ->
    iframe_samesite_script_6_constraints gb ->
    iframe_samesite_script_constraints gb ->
    evs = iframe_samesite_script_events ->
    st = iframe_samesite_script_state ->
    Reachable gb evs st ->
    LemmaQuery gb evs st.

InlineRelation is_secure_context             With Depth 1.
InlineRelation is_not_secure_context         With Depth 1.
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

Set Array Size 7.
Extract Query LemmaQuery.


