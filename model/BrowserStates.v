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

Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.


(******************************************************************************)
(* Utils                                                                      *)

Lemma map_none_is_none : forall A B (f: option A -> option B), f None = None ->
    map f ([|None|]) = ([|None|]).
Proof.
  intros. unfold map, select, const. rewrite H. reflexivity.
Qed.

Lemma render_none: forall (e : option HTMLElement),
    match e with
    | Some (HTMLForm m u) => False
    | _ => True
    end ->
    render_static_element e = None.
Proof.
  intros e. unfold render_static_element.
  destruct e. destruct h; auto. contradiction. reflexivity.
Qed.


(******************************************************************************)
(* Page with script                                                           *)


Definition script_state : State :=
  (Build_State 5
   (Build_FetchEngine 4 EmitterClient
    (Build_Request MethodGet
     (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))
     (Build_RequestHeaders None ([|None|]) None) None)
    1
    (Some
     (Build_Response
      (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))
      ResponseOk
      (Build_ResponseHeaders (Some ContentTypeScript)
       (Some
        (Build_SetCookie (NoPrefix 11) 12 None (subdomain 6 7)
         (anypath 5) false false SSStrict))
       (Some (TupleOrigin ProtocolHTTP (Some (domain 13)) (Some 14))) None None None)
      (Some
         (ContentElementScript
          (Build_Script
           (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5))) 4)))))
    ((([|None|]).[0] <- Some (EmitterClient, 0, 0))
              .[1] <- Some (EmitterClient, 1, 1)))
   (Build_ServiceWorker 0 ([|None|]))
   (Build_Window 0 None (Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash)) None
    (Build_Document 5 0
     (Build_ResponseHeaders (Some ContentTypeHTML) None None None None None)
     (Build_HTML 20 21
        (([|None|]).[0] <- (Some (HTMLScript
                               (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))))))
     (Build_DOM 0 0
        (([|None|]).[0] <- (Some (DOMElementResource
                               (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))
                               (ContentElementScript
                                  (Build_Script
                                     (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5))) 4)))))) empty_initiators))
   ((([|None|]).[0] <- Some (Build_SetCookie (NoPrefix 11) 12 None (subdomain 6 7)
                                             (anypath 5) false false SSStrict)))
  ([|None|]) ([|None|])).


Definition script_state_constraints (gb:Global) : Prop :=
     (server_responses gb).[0] = 0
  /\ (requests gb).[0] = (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash))
                          (Build_RequestHeaders None ([|None|]) None) None)
  /\ (responses gb).[0] = (Build_Response (Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash)) ResponseOk
                           (Build_ResponseHeaders (Some ContentTypeHTML) None None None None None)
                           (Some (ContentElementHTML
                           (Build_HTML 20 21
                            (([|None|]).[0] <-
                             (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5))))))))))
  /\ (server_responses gb).[1] = 1
  /\ (requests gb).[1] = (Build_Request MethodGet
                          (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))
                          (Build_RequestHeaders None ([|None|]) None) None)
  /\ (responses gb).[1] = (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))
                           ResponseOk
                           (Build_ResponseHeaders
                             (Some ContentTypeScript)
                             (Some
                                (Build_SetCookie (NoPrefix 11) 12 None (subdomain 6 7)
                                                 (anypath 5) false false SSStrict))
                             (Some (TupleOrigin ProtocolHTTP (Some (domain 13)) (Some 14))) None None None)
                           (Some (ContentElementScript
                                    (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5))) 4))))
  /\ (windows gb).[0] = (Build_Window 0 None (Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash)) None
                    (Build_Document 2 0
                     (Build_ResponseHeaders (Some ContentTypeHTML) None None None None None)
                     (Build_HTML 20 21
                       (([|None|]).[0] <- (Some (HTMLScript
                                         (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))))))
                     (Build_DOM 0 0 ([|None|]))
                     empty_initiators))
  /\  (windows gb).[1] = (st_window script_state)
  /\ c_origin_wide_csp (config gb) = false.


Definition script_state_events (gb: Global) : list Event := [
  EvDOMUpdate (DOMPath nil (DOMIndex 0));
  EvResponse ((responses gb).[1]) 1;
  EvRequest EmitterClient ((requests gb).[1]) 1;
  EvDOMUpdate (DOMPath nil DOMTopLevel);
  EvResponse ((responses gb).[0]) 0
].

Lemma script_state_is_reachable : forall gb,
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (map fst (origin_csp gb)) ->
    origin_csp gb.[0] = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None) ->
    script_state_constraints gb ->
    Reachable gb (script_state_events gb) script_state.
Proof.
  intros gb all_distinct_requests_gb all_distinct_responses_gb all_distinct_origin_gb initial_origin_gb H.
  unfold script_state_constraints in H.
  destruct H as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  unfold script_state.
  pose (wd_4 := (Build_Window 0 None (Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash)) None
                    (Build_Document 2 0
                     (Build_ResponseHeaders (Some ContentTypeHTML) None None None None None)
                     (Build_HTML 20 21
                       (([|None|]).[0] <- (Some (HTMLScript
                                         (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))))))
                     (Build_DOM 0 0 ([|None|])) empty_initiators))).

  eapply Event_dom_update
    with (rp := ((responses gb).[1]))
         (st_wd := wd_4)
         (st_bl := ([|None|])).
  - { apply Event_response
        with (st_ft := (Build_FetchEngine 3 EmitterClient
                                          ((requests gb.[1]))
                                          1 None
                                          (([|None|]).[0] <-
                                           Some (EmitterClient, 0, 0))))
             (st_cj := ([|None|])) (st_cj_e := ([|None|]))
             (wd_ctx := wd_4)
             (c_idx := 0) (rq_idx := 1) (rp_idx := 1).
      - { apply Event_request
            with (wd_ctx := wd_4)
                 (st_ft := (Build_FetchEngine 1 EmitterClient
                                              ((requests gb).[0]) 0 (Some ((responses gb).[0]))
                                              (([|None|]).[0] <-
                                               Some (EmitterClient, 0, 0)))).
          - { eapply Event_dom_update
                with (rp := ((responses gb).[0]))
                     (st_wd := initial_window)
                     (st_bl := ([|None|])).
              - { apply Event_response
                    with (st_ft := initial_fetch_engine)
                         (st_cj := ([|None|])) (st_cj_e := ([|None|]))
                         (wd_ctx := initial_window)
                         (c_idx := 0) (rq_idx := 0) (rp_idx := 0).
                  - apply Initial_state_is_reachable. assumption. assumption. assumption.
                    unfold initial_url. compute. assumption.
                  - unfold is_server_response. reflexivity.
                  - rewrite H1. reflexivity.
                  - constructor.
                    simpl. reflexivity.
                  - unfold is_valid_fetch_response. split. reflexivity. split. reflexivity.
                    split. rewrite H2. reflexivity. rewrite H2. reflexivity.
                  - rewrite H2. unfold is_server_response.
                    split. rewrite H1. unfold is_local_scheme. simpl. auto.
                    congruence.
                  - rewrite H1.  reflexivity.
                  - rewrite H2. reflexivity.
                }
              - destruct H6,a. rewrite e1. compute; auto.
              - eapply Render_window_base with (lz_pt := DOMTopLevel). reflexivity. apply H6.
                unfold render_window_dom_path_on_response.
                rewrite H2. simpl. split. exact I. split. reflexivity. split. exact I.
                unfold is_valid_response_content. simpl. split. auto. split. reflexivity.
                split. discriminate.
                unfold build_toplevel_window. simpl.
                assert (render_none_map:
                          map render_static_element
                              (([|None|]).[0]<- Some (HTMLScript
                                (Build_URL ProtocolHTTP (Some (subdomain 6 7)) (Some 8) (url_path_res (anypath 5)))))
                          = ([|None|]) ). {
                  unfold map, const, store, select.
                  apply functional_extensionality. destruct x; auto.
                }
                rewrite render_none_map. split. exact I. reflexivity.
              - reflexivity.
            }
          - reflexivity.
          - apply Emitter_window_contex. reflexivity.
          - unfold is_valid_emitter. exact I.
          - unfold is_valid_url. rewrite H4. exact I.
          - simpl. rewrite H2. simpl. rewrite H4. auto.
          - rewrite H4. simpl.
            rewrite map_none_is_none. reflexivity.
            unfold event_request_select_cookie. reflexivity.
          - reflexivity.
        }
      - reflexivity.
      - reflexivity.
      - apply Emitter_window_contex. simpl. reflexivity.
      - unfold is_valid_fetch_response. simpl.
        rewrite H4. rewrite H5. simpl. auto.
      - rewrite H5. simpl in *.
        unfold is_server_response. rewrite H3.
        unfold is_local_scheme. rewrite H4. auto.
      - simpl. rewrite H4. rewrite H5. simpl. auto.
      - rewrite H5. simpl. split.
        unfold is_valid_setcookie, check_secure_protocol, check_cookie_domain_set.
        simpl. auto. unfold cookiejar_erase_cookie. rewrite map_none_is_none. auto.
        unfold cookiejar_erase_cookie_mapfn. reflexivity.
    }
  - simpl. destruct H6,a. rewrite e1. compute;auto.
  - simpl. eapply Render_window_base with (lz_pt := DOMIndex 0). reflexivity. apply H6.
    unfold render_window_dom_path_on_response. rewrite H5. split. simpl. exact I.
    split. reflexivity. split. simpl. exact I. split.
    unfold is_valid_response_content. simpl. auto.
    split. reflexivity. split. discriminate. simpl.
    unfold select, store, const; auto.
  - reflexivity.
  Unshelve. all: constructor.
Qed.


(******************************************************************************)
(* Page with same site Iframe and two scripts: one in the frame, one outside  *)


Definition iframe_samesite_script_state := (Build_State 12 (Build_FetchEngine 11 EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) (Build_RequestHeaders None (const _ None) None) (Some 73)) 4 (Some (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) (Some (Build_SetCookie (NoPrefix 70) 71 None (subdomain 21 22) (anypath 72) false false SSStrict)) None (Some (Build_URL ProtocolHTTP None (Some 92) (url_path_data 93 94))) (Some (Build_CSP (Some (CSPSrcSource None None 95 (Some 96) None)) None)) None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) 11))))) (store _ (store _ (store _ (store _ (const _ None) 1 (Some (EmitterClient, 0, 0))) 2 (Some (EmitterClient, 1, 1))) 3 (Some (EmitterClient, 2, 2))) 4 (Some (EmitterClient, 3, 3)))) (Build_ServiceWorker 0 (const _ None)) (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) None (Build_Document 12 1 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 5) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))))))) 1 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) 11))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))) (Build_Initiators None (const _ None)))) (store _ (const _ None) 1 (Some (Build_SetCookie (NoPrefix 70) 71 None (subdomain 21 22) (anypath 72) false false SSStrict))) (const _ None) (const _ None)).

Definition iframe_samesite_script_state_6 := (Build_State 6 (Build_FetchEngine 5 EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) (Build_RequestHeaders None (const _ None) None) (Some 87)) 2 (Some (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict)) (Some (OpaqueOrigin 102)) (Some (Build_URL ProtocolHTTP None (Some 103) (url_path_data 104 105))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) None)) None) (Some (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 106) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))))))) (store _ (store _ (const _ None) 1 (Some (EmitterClient, 0, 0))) 2 (Some (EmitterClient, 1, 1)))) (Build_ServiceWorker 0 (const _ None)) (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) None (Build_Document 6 1 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (const _ None) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 106) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))) (Build_Initiators None (const _ None)))) (store _ (const _ None) 3 (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict))) (const _ None) (const _ None)).


Definition iframe_samesite_script_events := (cons (EvDOMUpdate (DOMPath nil (DOMIndex 1))) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) (Some (Build_SetCookie (NoPrefix 70) 71 None (subdomain 21 22) (anypath 72) false false SSStrict)) None (Some (Build_URL ProtocolHTTP None (Some 92) (url_path_data 93 94))) (Some (Build_CSP (Some (CSPSrcSource None None 95 (Some 96) None)) None)) None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) 11)))) 4) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) (Build_RequestHeaders None (const _ None) None) (Some 73)) 4) (cons (EvDOMUpdate (DOMPath (cons 0 nil) (DOMIndex 1))) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) None None (Some (Build_URL ProtocolHTTP None (Some 97) (url_path_data 98 99))) (Some (Build_CSP (Some (CSPSrcSource None None 100 (Some 101) None)) (Some (Build_TrustedTypes None false)))) None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) 8)))) 3) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) (Build_RequestHeaders None (store _ (const _ None) 3 (Some (Build_CookieMapping (NoPrefix 70) 75))) None) (Some 76)) 3) (cons (EvDOMUpdate (DOMPath nil (DOMIndex 0))) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict)) (Some (OpaqueOrigin 102)) (Some (Build_URL ProtocolHTTP None (Some 103) (url_path_data 104 105))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) None)) None) (Some (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 106) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129))))))))) 2) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) (Build_RequestHeaders None (const _ None) None) (Some 87)) 2) (cons (EvDOMUpdate (DOMPath nil DOMTopLevel)) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Some (ContentElementHTML (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))))) 1) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) (Build_RequestHeaders None (const _ None) None) (Some 77)) 1) nil)))))))))))).


Definition iframe_samesite_script_constraints gb :=
  (requests gb).[2] = (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) (Build_RequestHeaders None (store _ (const _ None) 3 (Some (Build_CookieMapping (NoPrefix 70) 75))) None) (Some 76)) /\
  (responses gb).[2] = (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) None None (Some (Build_URL ProtocolHTTP None (Some 97) (url_path_data 98 99))) (Some (Build_CSP (Some (CSPSrcSource None None 100 (Some 101) None)) (Some (Build_TrustedTypes None false)))) None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) 8)))) /\
  (server_responses gb).[2] = 2 /\
  (windows gb).[5] =
  (Build_Window 2 (Some 2) (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) None (Build_Document 9 2 (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict)) (Some (OpaqueOrigin 102)) (Some (Build_URL ProtocolHTTP None (Some 103) (url_path_data 104 105))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) None)) None) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))) (Build_DOM 2 0 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111)))))) 0 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114)))))) 1 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) 8))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120)))))) 4 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123)))))) 5 None) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129))))))) (Build_Initiators None (const _ None)))) /\
  (requests gb).[3] = (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) (Build_RequestHeaders None (const _ None) None) (Some 73)) /\
  (responses gb).[3] = (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) (Some (Build_SetCookie (NoPrefix 70) 71 None (subdomain 21 22) (anypath 72) false false SSStrict)) None (Some (Build_URL ProtocolHTTP None (Some 92) (url_path_data 93 94))) (Some (Build_CSP (Some (CSPSrcSource None None 95 (Some 96) None)) None)) None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) 11)))) /\
  (server_responses gb).[3] = 3 /\
  (windows gb).[4] = (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) None (Build_Document 12 1 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 5) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))))))) 1 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57))) 11))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))) (Build_Initiators None (const _ None)))).


Definition iframe_samesite_script_6_constraints (gb : Global) :=
   (requests gb).[0] = (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) (Build_RequestHeaders None (const _ None) None) (Some 77)) /\
  (responses gb).[0] = (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Some (ContentElementHTML (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))))) /\
  (server_responses gb).[0] = 0 /\
  (windows gb).[0] = (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) None (Build_Document 3 1 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) (Build_DOM 1 0 (store _ (store _ (store _ (const _ None) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))) (Build_Initiators None (const _ None)))) /\
  (requests gb).[1] = (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) (Build_RequestHeaders None (const _ None) None) (Some 87)) /\
  (responses gb).[1] = (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict)) (Some (OpaqueOrigin 102)) (Some (Build_URL ProtocolHTTP None (Some 103) (url_path_data 104 105))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) None)) None) (Some (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 106) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129))))))))) /\
  (server_responses gb).[1] = 1 /\
  (windows gb).[2] = (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 47 22)) (Some 48) (url_path_res (anypath 49))) None (Build_Document 6 1 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 50) (url_path_data 51 52))) (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 21)) 22 None None)) (Some (Build_TrustedTypes (Some (Some 53)) false)))) None) (Build_HTML 54 55 (store _ (store _ (store _ (store _ (store _ (store _ (const _ None) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 56) (url_path_res (anypath 57)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 64) (url_path_data 65 66))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (const _ None) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) 106) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))))) (Build_Initiators None (const _ None)))) /\
  (windows gb).[106] = (Build_Window 2 (Some 2) (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 86))) None (Build_Document 6 2 (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 70) 75 None (subdomain 21 22) (anypath 72) false false SSStrict)) (Some (OpaqueOrigin 102)) (Some (Build_URL ProtocolHTTP None (Some 103) (url_path_data 104 105))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) None)) None) (Build_HTML 107 108 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111))))) 0 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123))))) 5 (Some (HTMLImage (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))))) 6 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129)))))) (Build_DOM 2 0 (store _ (store _ (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 109) (url_path_data 110 111)))))) 0 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 112) (url_path_data 113 114)))))) 1 None) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 115) (url_path_data 116 117)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 118) (url_path_data 119 120)))))) 4 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 121) (url_path_data 122 123)))))) 5 None) 6 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 127) (url_path_data 128 129))))))) (Build_Initiators None (const _ None)))).
  
  
Lemma iframe_samesite_script_state_6_is_reachable : forall gb,
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (Array.map fst (origin_csp gb)) ->
    (origin_csp gb.[0]) = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None) ->
    c_origin_wide_csp (config gb) = false ->
    iframe_samesite_script_6_constraints gb ->
    Reachable gb (Coq.Lists.List.skipn 6 iframe_samesite_script_events)
              iframe_samesite_script_state_6.
Proof with simpl in *; try congruence.
  intros gb Hdrq Hdrp Hdo Hio Hcsp (Hrq0, (Hrp0, (Hsr0, (Hwd0, (Hrq1, (Hrp1, (Hsr1, (Hwd1, Hwd1f)))))))).
  compute.
  eapply Event_dom_update...
  eapply Event_response...
  eapply Event_request...
  eapply Event_dom_update...
  eapply Event_response...
  eapply Event_request...
  apply Initial_state_is_reachable.
  assumption. assumption. assumption. assumption.
  auto. firstorder. exact I. exact I. simpl in *; tauto. tauto. firstorder.
  apply (eq_sym Hrp0).
  apply (eq_sym Hrq0).
  firstorder; tauto. firstorder; tauto.
  split; [ rewrite Hrq0; tauto | rewrite Hsr0; apply Hrp0 ].
  firstorder. firstorder.
  rewrite Hcsp; auto.
  econstructor; firstorder...
  unfold build_toplevel_window. simpl. rewrite Hwd0. simpl.
  repeat f_equal.
  compute. apply functional_extensionality.
  intros x.
  destruct x as [ | [ | [ | [ | [ | [ | [ | _]]]]]]]...
  firstorder. auto...
  firstorder; auto. exact I. exact I. simpl in *; auto.
  firstorder; tauto. firstorder.
  apply (eq_sym Hrp1).
  apply (eq_sym Hrq1).
  firstorder; tauto. firstorder; tauto.
  split; [ rewrite Hrq1; tauto | rewrite Hsr1; apply Hrp1 ].
  reflexivity.
  split. compute; tauto.
  split; firstorder.
  instantiate (1 := 3). compute. tauto.
  rewrite Hcsp; auto.
  econstructor; firstorder...
  apply Hwd1. rewrite Hwd0. simpl.
  unfold update_page_element_at_idx. simpl.
  split. auto. split. split. exact I.
  rewrite Hwd1f. unfold build_toplevel_window. simpl.
  repeat f_equal. compute.
  apply functional_extensionality.
  intros x.
  destruct x as [ | [ | [ | [ | [ | [ | [ | _]]]]]]]...
  compute.
  repeat f_equal.
  apply functional_extensionality.
  intros x. induction x; tauto.
  reflexivity.
  Unshelve. all: repeat constructor.
Qed.


Lemma iframe_samesite_script_state_is_reachable : forall gb,
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (Array.map fst (origin_csp gb)) ->
    (origin_csp gb.[0]) = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None) ->
    c_origin_wide_csp (config gb) = false ->
    iframe_samesite_script_6_constraints gb ->
    iframe_samesite_script_constraints gb ->
    Reachable gb (iframe_samesite_script_events) iframe_samesite_script_state.
Proof with simpl in *; try congruence.
  intros gb Hdrq Hdrp Hdo Hio Hcsp Hs6 (Hrq2, (Hrp2, (Hsr2, (Hwd2, (Hrq3, (Hrp3, (Hsr3, Hwd4))))))).
  eapply Event_dom_update...
  eapply Event_response...
  eapply Event_request...
  eapply Event_dom_update...
  eapply Event_response...
  eapply Event_request...
  apply  iframe_samesite_script_state_6_is_reachable...
  assumption. assumption. assumption.
  auto. firstorder. exact I. exact I. simpl; auto.
  compute; simpl.
  apply functional_extensionality. intros x.
  destruct x as [ | [ | [ | [ | _]]]]...
  case_eq (Equality.eqb Domain (subdomain 21 22) (subdomain 21 22)); intros H'...
  case_eq (Equality.eqb nat 72 72); intros H1'...
  case_eq (Equality.eqb nat 22 22); intros H2'...
  assert (H2: 22 = 22) by reflexivity.
  rewrite <- Equality.eqb_eq in H2. congruence.
  assert (H2: 72 = 72) by reflexivity. rewrite <- Equality.eqb_eq in H2. congruence.
  assert (H2: (subdomain 21 22) = (subdomain 21 22)) by reflexivity. rewrite <- Equality.eqb_eq in H2. congruence.
  firstorder.
  apply (eq_sym Hrp2).
  apply (eq_sym Hrq2).
  firstorder. firstorder.
  split; [ rewrite Hrq2; tauto | rewrite Hsr2; apply Hrp2 ].
  firstorder. firstorder.
  rewrite Hcsp; auto.
  eapply Render_window_rec...
  firstorder.
  compute. firstorder.
  eapply Render_window_base...
  firstorder. 
  instantiate (2 := 5).
  firstorder. 
  firstorder.
  discriminate.
  destruct Hs6 as (_, (_, (_, (_, (_, (_, (_, (_, Hwd1f)))))))).
  unfold select in Hwd1f.
  compute. simpl.
  assert (HHHeq:
            ((html_body (dc_html (wd_document (windows gb 106)))) 1) = (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 74) (url_path_res (anypath 72)))))). {
    rewrite Hwd1f. tauto.
  }
  destruct ((html_body (dc_html (wd_document (windows gb 106))))).
  split. congruence. split. split. auto.
  assert (Hworkaround1:
            match rp_hd_csp (dc_headers (wd_document (windows gb 106))) with | Some c => match csp_script_src c with | Some csp_src => match match url_protocol (wd_location (windows gb 106)) with | ProtocolData => match url_path (wd_location (windows gb 106)) with | url_path_data nonce _ => Some (OpaqueOrigin nonce) | _ => None end | ProtocolBlob => match url_path (wd_location (windows gb 106)) with | url_path_blob org _ => Some org | _ => None end | _ => Some (TupleOrigin (url_protocol (wd_location (windows gb 106))) (url_host (wd_location (windows gb 106))) (url_port (wd_location (windows gb 106)))) end with | Some orign => match csp_src with | CSPSrcNone => False | CSPSrcSelf => Some orign = Some (TupleOrigin ProtocolHTTP (Some (subdomain 21 22)) (Some 74)) | CSPSrcScheme proto => ProtocolHTTP = proto | CSPSrcSource proto sub host port path => match proto with | Some p => ProtocolHTTP = p | None => True end /\ match sub with | Some (Some n) => 21 = n | Some None => True | None => False end /\ 22 = host /\ match port with | Some prt => Some 74 = Some prt | None => True end /\ match path with | Some pth => anypath 72 = pth | None => True end end | None => False end | None => True end | None => True end). {
    rewrite Hwd1f. simpl; tauto.
  }
  apply Hworkaround1.
  assert (Hworkaround2:
            windows gb 5 = {| wd_nonce := wd_nonce (windows gb 106); wd_parent := wd_parent (windows gb 106); wd_location := wd_location (windows gb 106); wd_document_domain := wd_document_domain (windows gb 106); wd_document := {| dc_version := 9; dc_nonce := dc_nonce (wd_document (windows gb 106)); dc_headers := dc_headers (wd_document (windows gb 106)); dc_html := dc_html (wd_document (windows gb 106)); dc_dom := {| dm_nonce := dm_nonce (dc_dom (wd_document (windows gb 106))); dm_head := dm_head (dc_dom (wd_document (windows gb 106))); dm_body := fun j : nat => if match j with | 1 => true | _ => false end then Some (DOMElementResource {| url_protocol := ProtocolHTTP; url_host := Some (subdomain 21 22); url_port := Some 74; url_path := url_path_res (anypath 72) |} (ContentElementScript {| script_src := {| url_protocol := ProtocolHTTP; url_host := Some (subdomain 21 22); url_port := Some 74; url_path := url_path_res (anypath 72) |}; script_nonce := 8 |})) else dm_body (dc_dom (wd_document (windows gb 106))) j |}; dc_init := dc_init (wd_document (windows gb 106)) |} |} ). {
    rewrite Hwd1f. unfold select in Hwd2. rewrite Hwd2. simpl. repeat f_equal.
    apply functional_extensionality. intros x. compute.
    destruct x as [ | [ | [ | [ | [ | [ | [ | _ ] ]]]]]]...
  }
  apply Hworkaround2.
  discriminate.
  firstorder.
  firstorder.
  firstorder. auto.
  firstorder. exact I. exact I.
  simpl. auto.
  compute. apply functional_extensionality.
  intros x. destruct x as [ | [ | [ | [ | _]]]]...
  case_eq (Equality.eqb Domain (subdomain 21 22) (subdomain 21 22)); intros H'...
  case_eq (Equality.eqb nat 57 72); intros H1'...
  case_eq (Equality.eqb nat 22 22); intros H2'...
  rewrite Equality.eqb_eq in H1'. discriminate.
  assert (H2'': 22 = 22) by reflexivity.
  rewrite <- Equality.eqb_eq in H2''. congruence.
  firstorder.
  apply (eq_sym Hrp3).
  apply (eq_sym Hrq3).
  firstorder. firstorder.
  split; [ rewrite Hrq3; tauto | rewrite Hsr3; apply Hrp3 ].
  firstorder. firstorder.
  compute.
  instantiate (1 := 1).
  compute. auto.
  compute. apply functional_extensionality. intros x.
  destruct x as [ | [ | [ | [ | _ ]]]]...
  case_eq (Equality.eqb CookieName (NoPrefix 70) (NoPrefix 70)); intros H'...
  case_eq (Equality.eqb Domain (subdomain 21 22) (subdomain 21 22)); intros H1'...
  case_eq (Equality.eqb Path (anypath 72) (anypath 72)); intros H2'...
  assert (Heq': anypath 72 = anypath 72) by reflexivity.
  rewrite <- Equality.eqb_eq in Heq'. congruence.
  assert (Heq': (subdomain 21 22) = (subdomain 21 22)) by reflexivity.
  rewrite <- Equality.eqb_eq in Heq'. congruence.
  assert (Heq': (NoPrefix 70) = (NoPrefix 70)) by reflexivity.
  rewrite <- Equality.eqb_eq in Heq'. congruence.
  rewrite Hcsp; auto.
  econstructor.
  firstorder.
  rewrite Hwd4. simpl. reflexivity.
  firstorder.
  discriminate.
  compute. repeat f_equal.
  apply functional_extensionality.
  intros x. compute.
  destruct x as [ | [ | [ | [ | [ | [ | [ | _ ] ]]]]]]...
  reflexivity.
  Unshelve. all: repeat econstructor.
Qed.


(******************************************************************************)
(* Extracted Lemmas                                                           *)


Definition hostquery_state_12 := (Build_State 12 (Build_FetchEngine 11 (EmitterScript (DOMPath nil (DOMIndex 1)) (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 13)) (Some 22) (url_path_res (anypath 23))) 8)) (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) (Build_RequestHeaders None (const _ None) None) (Some 28)) 4 (Some (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) ResponseOk (Build_ResponseHeaders (Some ContentTypeScript) (Some (Build_SetCookie (NoPrefix 29) 30 None (subdomain 24 25) (anypath 31) false false SSStrict)) None (Some (Build_URL ProtocolHTTP None (Some 32) (url_path_data 33 34))) None None) (Some (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) 11))))) (store _ (store _ (store _ (store _ (const _ None) 0 (Some (EmitterClient, 2, 3))) 1 (Some (EmitterClient, 3, 2))) 2 (Some (EmitterClient, 0, 4))) 3 (Some ((EmitterScript (DOMPath nil (DOMIndex 1)) (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 13)) (Some 22) (url_path_res (anypath 23))) 8)), 4, 0)))) (Build_ServiceWorker 0 (const _ None)) (Build_Window 1 None (Build_URL ProtocolHTTPS (Some (subdomain 21 13)) (Some 38) (url_path_res slash)) None (Build_Document 12 1 (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 39) 40 (Some (subdomain 21 13)) (subdomain 21 13) (anypath 41) false false SSStrict)) (Some (OpaqueOrigin 42)) (Some (Build_URL ProtocolHTTP None (Some 43) (url_path_data 44 45))) None None) (Build_HTML 47 48 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 49) (url_path_data 50 51))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTPS (Some (subdomain 52 13)) (Some 53) (url_path_res (anypath 54)))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 13)) (Some 22) (url_path_res (anypath 23)))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 55) (url_path_data 56 57))))) 3 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 58) (url_path_data 59 60))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 49) (url_path_data 50 51)))))) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTPS (Some (subdomain 52 13)) (Some 53) (url_path_res (anypath 54))) 0) (Build_HTML 65 66 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))) 0 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27)))))) 1 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 70) (url_path_data 71 72))))) 2 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 73) (url_path_data 74 75))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 76) (url_path_data 77 78))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 79) (url_path_data 80 81)))))))))) 1 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 21 13)) (Some 22) (url_path_res (anypath 23))) (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 21 13)) (Some 22) (url_path_res (anypath 23))) 8))))) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 55) (url_path_data 56 57)))))) 3 None) 4 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 61) (url_path_data 62 63))))))) (Build_Initiators None (const _ None)))) (store _ (store _ (store _ (const _ None) 0 (Some (Build_SetCookie (NoPrefix 29) 30 None (subdomain 24 25) (anypath 31) false false SSStrict))) 1 (Some (Build_SetCookie (NoPrefix 82) 83 None (subdomain 52 13) (anypath 84) false false SSStrict))) 2 (Some (Build_SetCookie (NoPrefix 39) 85 None (subdomain 21 13) (anypath 41) false false SSStrict))) (const _ None) (const _ None)).

Definition hostquery_state_12_constraints gb :=
  (windows gb).[0] = (Build_Window 2 (Some 0) (Build_URL ProtocolHTTPS (Some (subdomain 52 13)) (Some 53) (url_path_res (anypath 54))) None (Build_Document 12 2 (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 82) 83 None (subdomain 52 13) (anypath 84) false false SSStrict)) None (Some (Build_URL ProtocolHTTP None (Some 124) (url_path_data 125 126))) None None) (Build_HTML 65 66 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69))))) 0 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27)))))) 1 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 70) (url_path_data 71 72))))) 2 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 73) (url_path_data 74 75))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 76) (url_path_data 77 78))))) 4 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 79) (url_path_data 80 81)))))) (Build_DOM 2 0 (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 67) (url_path_data 68 69)))))) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) (ContentElementScript (Build_Script (Build_URL ProtocolHTTP (Some (subdomain 24 25)) (Some 26) (url_path_res (anypath 27))) 11))))) 1 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 70) (url_path_data 71 72)))))) 2 None) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 76) (url_path_data 77 78)))))) 4 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 79) (url_path_data 80 81))))))) (Build_Initiators None (const _ None)))).

Lemma extracted_lemma_hostquery_state12 : forall gb,
    hostquery_state_12_constraints gb ->
    Reachable gb ([EvDOMUpdate (DOMPath [0] (DOMIndex 0))]) hostquery_state_12.
Proof. Admitted.


Definition cspquery_state_6 := (Build_State 6 (Build_FetchEngine 5 EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) (Build_RequestHeaders None (const _ None) None) (Some 73)) 2 (Some (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 120) (url_path_data 121 122))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) (Some (Build_TrustedTypes (Some (Some 123)) false)))) None) (Some (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) 2) (Build_HTML 58 59 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 60) (url_path_data 61 62))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 63) (url_path_data 64 65))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 24)))))) 2 None) 3 None) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 66) (url_path_data 67 68)))))))))) (store _ (store _ (const _ None) 0 (Some (EmitterClient, 3, 1))) 1 (Some (EmitterClient, 0, 3)))) (Build_ServiceWorker 0 (const _ None)) (Build_Window 1 None (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 33))) None (Build_Document 6 1 (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 34) 35 None (subdomain 30 31) (anypath 36) false false SSStrict)) None None (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 37)) 38 None None)) (Some (Build_TrustedTypes (Some (Some 39)) false)))) None) (Build_HTML 40 41 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 42) (url_path_data 43 44))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45)))))) 1 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 46) (url_path_data 47 48))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 49) (url_path_data 50 51))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 52) (url_path_data 53 54))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 99) (url_path_data 100 101)))))) (Build_DOM 1 0 (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 42) (url_path_data 43 44)))))) 0 (Some (DOMElementResource (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) 2) (Build_HTML 58 59 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 60) (url_path_data 61 62))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 63) (url_path_data 64 65))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 24)))))) 2 None) 3 None) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 66) (url_path_data 67 68)))))))))) 1 None) 2 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 49) (url_path_data 50 51)))))) 3 (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 52) (url_path_data 53 54)))))) 4 None)) (Build_Initiators None (const _ None)))) (store _ (const _ None) 0 (Some (Build_SetCookie (NoPrefix 34) 35 None (subdomain 30 31) (anypath 36) false false SSStrict))) (const _ None) (const _ None)).

Definition cspquery_state_6_events := (cons (EvDOMUpdate (DOMPath nil (DOMIndex 0))) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 120) (url_path_data 121 122))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) (Some (Build_TrustedTypes (Some (Some 123)) false)))) None) (Some (ContentElementFrame (Build_Frame (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) 2) (Build_HTML 58 59 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 60) (url_path_data 61 62))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 63) (url_path_data 64 65))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 24)))))) 2 None) 3 None) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 66) (url_path_data 67 68))))))))) 2) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) (Build_RequestHeaders None (const _ None) None) (Some 73)) 2) (cons (EvDOMUpdate (DOMPath nil DOMTopLevel)) (cons (EvResponse (Build_Response (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 33))) ResponseOk (Build_ResponseHeaders (Some ContentTypeHTML) (Some (Build_SetCookie (NoPrefix 34) 35 None (subdomain 30 31) (anypath 36) false false SSStrict)) None None (Some (Build_CSP (Some (CSPSrcSource None (Some (Some 37)) 38 None None)) (Some (Build_TrustedTypes (Some (Some 39)) false)))) None) (Some (ContentElementHTML (Build_HTML 40 41 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 42) (url_path_data 43 44))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45)))))) 1 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 46) (url_path_data 47 48))))) 2 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 49) (url_path_data 50 51))))) 3 (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 52) (url_path_data 53 54))))) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 99) (url_path_data 100 101))))))))) 1) (cons (EvRequest EmitterClient (Build_Request MethodGet (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 33))) (Build_RequestHeaders None (const _ None) None) (Some 79)) 1) nil)))))).

Definition cspquery_state_6_constraints gb :=
  (windows gb).[2] = (Build_Window 2 (Some 3) (Build_URL ProtocolHTTP (Some (subdomain 30 31)) (Some 32) (url_path_res (anypath 45))) None (Build_Document 6 2 (Build_ResponseHeaders (Some ContentTypeHTML) None None (Some (Build_URL ProtocolHTTP None (Some 120) (url_path_data 121 122))) (Some (Build_CSP (Some (CSPSrcSource None (Some None) 22 None None)) (Some (Build_TrustedTypes (Some (Some 123)) false)))) None) (Build_HTML 58 59 (store _ (store _ (store _ (store _ (store _ (const _ (Some (HTMLForm MethodGet (Build_URL ProtocolHTTP None (Some 60) (url_path_data 61 62))))) 0 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 63) (url_path_data 64 65))))) 1 (Some (HTMLScript (Build_URL ProtocolHTTP (Some (subdomain 21 22)) (Some 23) (url_path_res (anypath 24)))))) 2 None) 3 None) 4 (Some (HTMLFrame (Build_URL ProtocolHTTP None (Some 66) (url_path_data 67 68)))))) (Build_DOM 2 0 (store _ (store _ (store _ (store _ (store _ (const _ (Some (DOMElementForm (Build_Form MethodGet (Build_URL ProtocolHTTP None (Some 60) (url_path_data 61 62)))))) 0 None) 1 None) 2 None) 3 None) 4 None)) (Build_Initiators None (const _ None)))).


Lemma extracted_lemma_cspquery : forall gb,
    cspquery_state_6_constraints gb -> Reachable gb (cspquery_state_6_events) cspquery_state_6.
Proof. Admitted.
