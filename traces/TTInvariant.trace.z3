
(let ((a!1 (asserted (forall ((A listEvent)
                              (B NestedDOMPath)
                              (C Int)
                              (D Window)
                              (E HTML)
                              (F Frame)
                              (G listInt)
                              (H DOMSelector)
                              (I Window)
                              (J Window)
                              (K Global)
                              (L Global)
                              (M NestedDOMPath)
                              (N DOMSelector)
                              (O Window)
                              (P Window)
                              (Q Global)
                              (R NestedDOMPath)
                              (S DOMSelector)
                              (T Window)
                              (U Window)
                              (V listInt)
                              (W Int)
                              (X Window)
                              (Y NestedDOMPath)
                              (Z Int)
                              (A1 Window)
                              (B1 HTML)
                              (C1 Frame)
                              (D1 listInt)
                              (E1 DOMSelector)
                              (F1 Window)
                              (G1 Window)
                              (H1 Global)
                              (I1 Global)
                              (J1 NestedDOMPath)
                              (K1 DOMSelector)
                              (L1 Window)
                              (M1 Window)
                              (N1 NestedDOMPath)
                              (O1 Window)
                              (P1 Global)
                              (Q1 Global)
                              (R1 NestedDOMPath)
                              (S1 DOMSelector)
                              (T1 Window)
                              (U1 Window)
                              (V1 Window)
                              (W1 Response)
                              (X1 Request)
                              (Y1 Int)
                              (Z1 Response)
                              (A2 Request)
                              (B2 Int)
                              (C2 Response)
                              (D2 Request)
                              (E2 Int)
                              (F2 listEvent)
                              (G2 State))
                       (! (let ((a!1 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document V1)))))
                                (a!2 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      DOMTopLevel))
                                                (consEvent (EvResponse C2 E2)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 D2
                                                                                 E2)
                                                                      nilEvent))))
                                (a!6 (consEvent (EvScriptUpdateHTML
                                                  (DOMPath V (DOMIndex W))
                                                  N1
                                                  V1)
                                                A))
                                (a!7 ((_ is SomeCSP)
                                       (rp_hd_csp (dc_headers (wd_document V1)))))
                                (a!9 (@0ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!10 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!11 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!12 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!13 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!14 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!19 (and (= X T)
                                           (= T U)
                                           (= (st_window G2) U)
                                           (= R (DOMPath nilInt S))
                                           (= (DOMPath V (DOMIndex W)) R)
                                           (= P1 Q)))
                                (a!20 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!21 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!22 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!23 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!24 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!25 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document D)))))
                                (a!33 (ite (= (frame_window F) 3)
                                           (@3ArrayWindow (windows K))
                                           (ite (= (frame_window F) 4)
                                                (@4ArrayWindow (windows K))
                                                (@defaultArrayWindow
                                                  (windows K)))))
                                (a!37 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!38 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!39 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!40 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!41 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!42 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document A1)))))
                                (a!50 (ite (= (frame_window C1) 3)
                                           (@3ArrayWindow (windows H1))
                                           (ite (= (frame_window C1) 4)
                                                (@4ArrayWindow (windows H1))
                                                (@defaultArrayWindow
                                                  (windows H1))))))
                          (let ((a!3 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      (DOMIndex 0)))
                                                (consEvent (EvResponse Z1 B2)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 A2
                                                                                 B2)
                                                                      a!2))))
                                (a!8 ((_ is SomeoptionInt)
                                       (tt_policy (@0SomeTrustedTypes
                                                    (csp_trusted_types a!1)))))
                                (a!15 (ite (= W 2)
                                           a!11
                                           (ite (= W 3)
                                                a!12
                                                (ite (= W 4) a!13 a!14))))
                                (a!26 (ite (= C 2)
                                           a!22
                                           (ite (= C 3)
                                                a!23
                                                (ite (= C 4) a!24 a!25))))
                                (a!34 (ite (= (frame_window F) 1)
                                           (@1ArrayWindow (windows K))
                                           (ite (= (frame_window F) 2)
                                                (@2ArrayWindow (windows K))
                                                a!33)))
                                (a!43 (ite (= Z 2)
                                           a!39
                                           (ite (= Z 3)
                                                a!40
                                                (ite (= Z 4) a!41 a!42))))
                                (a!51 (ite (= (frame_window C1) 1)
                                           (@1ArrayWindow (windows H1))
                                           (ite (= (frame_window C1) 2)
                                                (@2ArrayWindow (windows H1))
                                                a!50)))
                                (a!55 (@0SomeoptionInt (tt_policy (@0SomeTrustedTypes
                                                                    (csp_trusted_types
                                                                      a!1))))))
                          (let ((a!4 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                               nilInt)
                                                                      (DOMIndex 1)))
                                                (consEvent (EvResponse W1 Y1)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 X1
                                                                                 Y1)
                                                                      a!3))))
                                (a!16 (ite (= W 0) a!9 (ite (= W 1) a!10 a!15)))
                                (a!27 (ite (= C 0) a!20 (ite (= C 1) a!21 a!26)))
                                (a!35 (= (ite (= (frame_window F) 0)
                                              (@0ArrayWindow (windows K))
                                              a!34)
                                         I))
                                (a!44 (ite (= Z 0) a!37 (ite (= Z 1) a!38 a!43)))
                                (a!52 (= (ite (= (frame_window C1) 0)
                                              (@0ArrayWindow (windows H1))
                                              a!51)
                                         F1)))
                          (let ((a!5 (consEvent (EvScriptUpdateHTML
                                                  (DOMPath (consInt 0 nilInt)
                                                           (DOMIndex 1))
                                                  (DOMPath nilInt (DOMIndex 3))
                                                  V1)
                                                a!4))
                                (a!17 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!16)))))
                                (a!18 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!16)))))
                                (a!28 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!27)))
                                         F))
                                (a!29 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!27)))
                                         E))
                                (a!30 (not ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!27)))))
                                (a!31 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!27)))))
                                (a!32 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!27)))))
                                (a!45 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!44)))
                                         C1))
                                (a!46 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!44)))
                                         B1))
                                (a!47 (not ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!44)))))
                                (a!48 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!44)))))
                                (a!49 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!44))))))
                          (let ((a!36 (and a!28
                                           a!29
                                           a!30
                                           a!31
                                           a!32
                                           (not ((_ is DOMElementForm)
                                                  (@0SomeDOMElement a!27)))
                                           ((_ is SomeDOMElement) a!27)
                                           (= I P)
                                           (= J O)
                                           (= X J)
                                           (= O P)
                                           a!35
                                           (= (st_window G2) D)
                                           (= M (DOMPath G H))
                                           (= M (DOMPath nilInt N))
                                           (= B (DOMPath (consInt C G) H))
                                           (= (DOMPath V (DOMIndex W)) B)
                                           (= P1 K)
                                           (= K L)))
                                (a!53 (and a!45
                                           a!46
                                           a!47
                                           a!48
                                           a!49
                                           (not ((_ is DOMElementForm)
                                                  (@0SomeDOMElement a!44)))
                                           ((_ is SomeDOMElement) a!44)
                                           (= O1 G1)
                                           (= G1 L1)
                                           (= F1 M1)
                                           (= L1 M1)
                                           a!52
                                           (= (st_window G2) A1)
                                           (= N1 Y)
                                           (= J1 (DOMPath D1 E1))
                                           (= J1 (DOMPath nilInt K1))
                                           (= Y (DOMPath (consInt Z D1) E1))
                                           (= P1 H1)
                                           (= H1 I1))))
                          (let ((a!54 (or (and (= O1 T1)
                                               (= T1 U1)
                                               (= (st_window G2) U1)
                                               (= N1 R1)
                                               (= R1 (DOMPath nilInt S1))
                                               (= P1 Q1))
                                          a!53)))
                          (let ((a!56 (and (Reachable P1 F2 G2)
                                           ((_ is SomeTrustedTypes)
                                             (csp_trusted_types a!1))
                                           ((_ is Build_CSP) a!1)
                                           (= F2 a!5)
                                           (= F2 a!6)
                                           a!7
                                           a!8
                                           ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location V1)))
                                           ((_ is SomeDOMElement) a!16)
                                           (not ((_ is DOMElementForm)
                                                  (@0SomeDOMElement a!16)))
                                           a!17
                                           a!18
                                           ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!16)))
                                           (not (c_tt_strict_realm_check
                                                  (config P1)))
                                           (c_restrict_tt_to_secure_contexts
                                             (config P1))
                                           (tt_require_for_script
                                             (@0SomeTrustedTypes
                                               (csp_trusted_types a!1)))
                                           (or a!19 a!36)
                                           a!54
                                           ((_ is NoneInt) a!55))))
                            (=> a!56 (query!0 G2 F2 P1)))))))))
                          :weight 0))))
      (a!3 (asserted (forall ((A State)
                              (B listEvent)
                              (C NestedDOMPath)
                              (D Int)
                              (E Window)
                              (F HTML)
                              (G Frame)
                              (H listInt)
                              (I DOMSelector)
                              (J Window)
                              (K Window)
                              (L Global)
                              (M Global)
                              (N NestedDOMPath)
                              (O DOMSelector)
                              (P Window)
                              (Q Window)
                              (R Global)
                              (S NestedDOMPath)
                              (T DOMSelector)
                              (U Window)
                              (V Window)
                              (W NestedDOMPath)
                              (X listInt)
                              (Y Int)
                              (Z Window)
                              (A1 Script)
                              (B1 NestedDOMPath)
                              (C1 Int)
                              (D1 Window)
                              (E1 HTML)
                              (F1 Frame)
                              (G1 listInt)
                              (H1 DOMSelector)
                              (I1 Window)
                              (J1 Window)
                              (K1 Global)
                              (L1 Global)
                              (M1 NestedDOMPath)
                              (N1 DOMSelector)
                              (O1 Window)
                              (P1 Window)
                              (Q1 NestedDOMPath)
                              (R1 Window)
                              (S1 Window)
                              (T1 Global)
                              (U1 Global)
                              (V1 NestedDOMPath)
                              (W1 DOMSelector)
                              (X1 Window)
                              (Y1 Window)
                              (Z1 NestedDOMPath)
                              (A2 Int)
                              (B2 Window)
                              (C2 HTML)
                              (D2 Frame)
                              (E2 listInt)
                              (F2 DOMSelector)
                              (G2 Window)
                              (H2 Global)
                              (I2 Global)
                              (J2 NestedDOMPath)
                              (K2 DOMSelector)
                              (L2 Window)
                              (M2 Global)
                              (N2 NestedDOMPath)
                              (O2 DOMSelector)
                              (P2 Window)
                              (Q2 HTMLElement)
                              (R2 Script)
                              (S2 NestedDOMPath)
                              (T2 State)
                              (U2 Global)
                              (V2 NestedDOMPath)
                              (W2 Int)
                              (X2 Window)
                              (Y2 HTML)
                              (Z2 Frame)
                              (A3 listInt)
                              (B3 DOMSelector)
                              (C3 Window)
                              (D3 Window)
                              (E3 Global)
                              (F3 Global)
                              (G3 NestedDOMPath)
                              (H3 DOMSelector)
                              (I3 Window)
                              (J3 Window)
                              (K3 Window)
                              (L3 Global)
                              (M3 Global)
                              (N3 NestedDOMPath)
                              (O3 DOMSelector)
                              (P3 Window)
                              (Q3 Window)
                              (R3 NestedDOMPath)
                              (S3 listInt)
                              (T3 Int)
                              (U3 Window)
                              (V3 Script)
                              (W3 optionInt)
                              (X3 Int)
                              (Y3 TrustedTypes)
                              (Z3 CSP)
                              (A4 Window)
                              (B4 NestedDOMPath)
                              (C4 Int)
                              (D4 HTML)
                              (E4 Frame)
                              (F4 Window)
                              (G4 NestedDOMPath)
                              (H4 listInt)
                              (I4 DOMSelector)
                              (J4 Int)
                              (K4 HTML)
                              (L4 Frame)
                              (M4 Global)
                              (N4 Window)
                              (O4 Window)
                              (P4 listInt)
                              (Q4 DOMSelector)
                              (R4 Window)
                              (S4 Global)
                              (T4 Global)
                              (U4 NestedDOMPath)
                              (V4 DOMSelector)
                              (W4 Window)
                              (X4 Global)
                              (Y4 NestedDOMPath)
                              (Z4 DOMSelector)
                              (A5 Window)
                              (B5 HTMLElement)
                              (C5 State)
                              (D5 Script)
                              (E5 NestedDOMPath)
                              (F5 State)
                              (G5 Global)
                              (H5 NestedDOMPath)
                              (I5 Int)
                              (J5 Window)
                              (K5 HTML)
                              (L5 Frame)
                              (M5 listInt)
                              (N5 DOMSelector)
                              (O5 Window)
                              (P5 Window)
                              (Q5 Global)
                              (R5 Global)
                              (S5 NestedDOMPath)
                              (T5 DOMSelector)
                              (U5 Window)
                              (V5 Window)
                              (W5 Window)
                              (X5 Global)
                              (Y5 Global)
                              (Z5 NestedDOMPath)
                              (A6 DOMSelector)
                              (B6 Window)
                              (C6 Window)
                              (D6 NestedDOMPath)
                              (E6 listInt)
                              (F6 Int)
                              (G6 Window)
                              (H6 Script)
                              (I6 optionInt)
                              (J6 Int)
                              (K6 TrustedTypes)
                              (L6 CSP)
                              (M6 Window)
                              (N6 TrustedTypes)
                              (O6 CSP)
                              (P6 Window)
                              (Q6 NestedDOMPath)
                              (R6 HTML)
                              (S6 listInt)
                              (T6 DOMSelector)
                              (U6 HTMLElement)
                              (V6 Window)
                              (W6 Global)
                              (X6 NestedDOMPath)
                              (Y6 Window)
                              (Z6 Window)
                              (A7 Int)
                              (B7 Int)
                              (C7 HTMLElement)
                              (D7 Window)
                              (E7 Global)
                              (F7 Window)
                              (G7 Int)
                              (H7 Int)
                              (I7 Window)
                              (J7 Frame)
                              (K7 Int)
                              (L7 Window)
                              (M7 Window)
                              (N7 HTMLElement)
                              (O7 Global)
                              (P7 NestedDOMPath)
                              (Q7 Window)
                              (R7 Window)
                              (S7 Int)
                              (T7 Int)
                              (U7 HTMLElement)
                              (V7 Window)
                              (W7 NestedDOMPath)
                              (X7 listInt)
                              (Y7 DOMSelector)
                              (Z7 optionInt)
                              (A8 Int)
                              (B8 Global)
                              (C8 NestedDOMPath)
                              (D8 Window)
                              (E8 Int)
                              (F8 optionInt)
                              (G8 Window)
                              (H8 Global)
                              (I8 Window)
                              (J8 Window)
                              (K8 Int)
                              (L8 Int)
                              (M8 Window)
                              (N8 Frame)
                              (O8 Int)
                              (P8 HTML)
                              (Q8 Window)
                              (R8 Window)
                              (S8 Int)
                              (T8 Global)
                              (U8 NestedDOMPath)
                              (V8 Window)
                              (W8 Int)
                              (X8 optionInt)
                              (Y8 Window)
                              (Z8 listEvent)
                              (A9 Int)
                              (B9 FetchEngine)
                              (C9 ServiceWorker)
                              (D9 Window)
                              (E9 ArrayoptionSetCookie)
                              (F9 ArrayoptionBlob)
                              (G9 ArrayoptionStorageItem))
                       (! (let ((a!1 (Build_State (+ 1 A9) B9 C9 D9 E9 F9 G9))
                                (a!2 (@0ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!3 (@1ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!4 (@2ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!5 (@3ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!6 (@4ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!7 (@defaultArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document Z)))))
                                (a!13 (and ((_ is SomeDomain)
                                             (wd_document_domain Q7))
                                           (= (url_protocol (wd_location V7))
                                              (url_protocol (wd_location Q7)))
                                           (= (@0SomeDomain (wd_document_domain
                                                              V7))
                                              (@0SomeDomain (wd_document_domain
                                                              Q7)))))
                                (a!14 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location V7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location V7)))))
                                (a!15 (SomeOrigin (TupleOrigin (url_protocol (wd_location V7))
                                                               (url_host (wd_location V7))
                                                               (url_port (wd_location V7)))))
                                (a!16 (OpaqueOrigin (@0url_path_data (url_path (wd_location V7)))))
                                (a!18 (SomeOrigin (@0url_path_blob (url_path (wd_location V7)))))
                                (a!22 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location Q7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location Q7)))))
                                (a!23 (SomeOrigin (TupleOrigin (url_protocol (wd_location Q7))
                                                               (url_host (wd_location Q7))
                                                               (url_port (wd_location Q7)))))
                                (a!24 (OpaqueOrigin (@0url_path_data (url_path (wd_location Q7)))))
                                (a!26 (SomeOrigin (@0url_path_blob (url_path (wd_location Q7)))))
                                (a!31 (@1ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!32 (@2ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!33 (@3ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!34 (@4ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!35 (@defaultArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!36 (@0ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!41 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm U7)
                                                                                  (@1HTMLForm U7)))))
                                (a!43 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!44 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!45 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!46 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!47 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!48 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!54 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!55 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!56 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!57 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!58 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!59 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!65 (and ((_ is SomeDomain)
                                             (wd_document_domain Y6))
                                           (= (url_protocol (wd_location D7))
                                              (url_protocol (wd_location Y6)))
                                           (= (@0SomeDomain (wd_document_domain
                                                              D7))
                                              (@0SomeDomain (wd_document_domain
                                                              Y6)))))
                                (a!66 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location D7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location D7)))))
                                (a!67 (SomeOrigin (TupleOrigin (url_protocol (wd_location D7))
                                                               (url_host (wd_location D7))
                                                               (url_port (wd_location D7)))))
                                (a!68 (OpaqueOrigin (@0url_path_data (url_path (wd_location D7)))))
                                (a!70 (SomeOrigin (@0url_path_blob (url_path (wd_location D7)))))
                                (a!74 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location Y6)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location Y6)))))
                                (a!75 (SomeOrigin (TupleOrigin (url_protocol (wd_location Y6))
                                                               (url_host (wd_location Y6))
                                                               (url_port (wd_location Y6)))))
                                (a!76 (OpaqueOrigin (@0url_path_data (url_path (wd_location Y6)))))
                                (a!78 (SomeOrigin (@0url_path_blob (url_path (wd_location Y6)))))
                                (a!85 (DOMElementResource
                                        (wd_location I7)
                                        (ContentElementFrame
                                          (Build_Frame (frame_src J7) K7)
                                          (dc_html (wd_document L7)))))
                                (a!91 (@1ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!92 (@2ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!93 (@3ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!94 (@4ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!95 (@defaultArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!96 (@0ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!101 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm C7)
                                                                                   (@1HTMLForm C7)))))
                                (a!103 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!104 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!105 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!106 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!107 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!108 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!113 (ite (= K7 3)
                                            (@3ArrayWindow (windows E7))
                                            (ite (= K7 4)
                                                 (@4ArrayWindow (windows E7))
                                                 (@defaultArrayWindow
                                                   (windows E7)))))
                                (a!116 (ite (= (frame_window J7) 3)
                                            (@3ArrayWindow (windows E7))
                                            (ite (= (frame_window J7) 4)
                                                 (@4ArrayWindow (windows E7))
                                                 (@defaultArrayWindow
                                                   (windows E7)))))
                                (a!120 (@1ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!121 (@2ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!122 (@3ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!123 (@4ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!124 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document Y8)))))
                                (a!125 (@0ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!131 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!132 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!133 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!134 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!135 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!136 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!144 (DOMElementResource
                                         (wd_location M8)
                                         (ContentElementFrame
                                           (Build_Frame (frame_src N8) O8)
                                           P8)))
                                (a!150 (@1ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!151 (@2ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!152 (@3ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!153 (@4ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!154 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document G8)))))
                                (a!155 (@0ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!160 (ite (= O8 3)
                                            (@3ArrayWindow (windows H8))
                                            (ite (= O8 4)
                                                 (@4ArrayWindow (windows H8))
                                                 (@defaultArrayWindow
                                                   (windows H8)))))
                                (a!163 (ite (= (frame_window N8) 3)
                                            (@3ArrayWindow (windows H8))
                                            (ite (= (frame_window N8) 4)
                                                 (@4ArrayWindow (windows H8))
                                                 (@defaultArrayWindow
                                                   (windows H8)))))
                                (a!167 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!168 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!169 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!170 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!171 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!172 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!180 (ite (= (frame_window G) 3)
                                            (@3ArrayWindow (windows L))
                                            (ite (= (frame_window G) 4)
                                                 (@4ArrayWindow (windows L))
                                                 (@defaultArrayWindow
                                                   (windows L)))))
                                (a!185 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!186 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!187 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!188 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!189 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!190 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!198 (ite (= (frame_window F1) 3)
                                            (@3ArrayWindow (windows K1))
                                            (ite (= (frame_window F1) 4)
                                                 (@4ArrayWindow (windows K1))
                                                 (@defaultArrayWindow
                                                   (windows K1)))))
                                (a!203 (or (and (c_tt_strict_realm_check
                                                  (config T1))
                                                (= P6 S1))
                                           (not (c_tt_strict_realm_check
                                                  (config T1)))))
                                (a!204 (= (rp_hd_csp (dc_headers (wd_document S1)))
                                          NoneCSP))
                                (a!205 (not (= (url_protocol (wd_location A5))
                                               ProtocolHTTPS)))
                                (a!206 (not (= (url_protocol (wd_location F4))
                                               ProtocolHTTPS)))
                                (a!207 (not (= (url_protocol (wd_location W4))
                                               ProtocolHTTPS)))
                                (a!208 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!209 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!210 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!211 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!212 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!213 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document O4)))))
                                (a!221 (ite (= (frame_window L4) 3)
                                            (@3ArrayWindow (windows M4))
                                            (ite (= (frame_window L4) 4)
                                                 (@4ArrayWindow (windows M4))
                                                 (@defaultArrayWindow
                                                   (windows M4)))))
                                (a!224 (not (= (url_protocol (wd_location O4))
                                               ProtocolHTTPS)))
                                (a!227 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!228 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!229 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!230 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!231 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!232 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!240 (ite (= (frame_window E4) 3)
                                            (@3ArrayWindow (windows S4))
                                            (ite (= (frame_window E4) 4)
                                                 (@4ArrayWindow (windows S4))
                                                 (@defaultArrayWindow
                                                   (windows S4)))))
                                (a!244 (= (rp_hd_csp (dc_headers (wd_document A4)))
                                          NoneCSP))
                                (a!245 (or (= (tt_policy Y3) NoneoptionInt)
                                           (and (= W3 (SomeInt X3))
                                                (= (tt_policy Y3)
                                                   (SomeoptionInt W3)))))
                                (a!247 (= (rp_hd_csp (dc_headers (wd_document A4)))
                                          (SomeCSP Z3)))
                                (a!248 (and (= R1 P2)
                                            (= N2 (DOMPath nilInt O2))
                                            (= Q1 N2)
                                            (= T1 M2)
                                            (= (url_protocol (wd_location P2))
                                               ProtocolHTTPS)))
                                (a!249 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!250 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!251 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!252 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!253 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!254 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!262 (ite (= (frame_window D2) 3)
                                            (@3ArrayWindow (windows H2))
                                            (ite (= (frame_window D2) 4)
                                                 (@4ArrayWindow (windows H2))
                                                 (@defaultArrayWindow
                                                   (windows H2)))))
                                (a!266 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!267 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!268 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!269 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!270 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!271 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!279 (ite (= (frame_window Z2) 3)
                                            (@3ArrayWindow (windows E3))
                                            (ite (= (frame_window Z2) 4)
                                                 (@4ArrayWindow (windows E3))
                                                 (@defaultArrayWindow
                                                   (windows E3)))))
                                (a!284 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!285 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!286 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!287 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!288 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!289 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!297 (= (rp_hd_csp (dc_headers (wd_document M6)))
                                          NoneCSP))
                                (a!298 (or (= (tt_policy K6) NoneoptionInt)
                                           (and (= I6 (SomeInt J6))
                                                (= (tt_policy K6)
                                                   (SomeoptionInt I6)))))
                                (a!300 (= (rp_hd_csp (dc_headers (wd_document M6)))
                                          (SomeCSP L6)))
                                (a!301 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!302 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!303 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!304 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!305 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!306 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!314 (ite (= (frame_window L5) 3)
                                            (@3ArrayWindow (windows Q5))
                                            (ite (= (frame_window L5) 4)
                                                 (@4ArrayWindow (windows Q5))
                                                 (@defaultArrayWindow
                                                   (windows Q5)))))
                                (a!319 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!320 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!321 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!322 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!323 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!324 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!333 (= (rp_hd_csp (dc_headers (wd_document S1)))
                                          (SomeCSP O6))))
                          (let ((a!8 (ite (= Y 2)
                                          a!4
                                          (ite (= Y 3)
                                               a!5
                                               (ite (= Y 4) a!6 a!7))))
                                (a!17 (ite ((_ is url_path_data)
                                             (url_path (wd_location V7)))
                                           (SomeOrigin a!16)
                                           NoneOrigin))
                                (a!19 (ite ((_ is url_path_blob)
                                             (url_path (wd_location V7)))
                                           a!18
                                           NoneOrigin))
                                (a!25 (ite ((_ is url_path_data)
                                             (url_path (wd_location Q7)))
                                           (SomeOrigin a!24)
                                           NoneOrigin))
                                (a!27 (ite ((_ is url_path_blob)
                                             (url_path (wd_location Q7)))
                                           a!26
                                           NoneOrigin))
                                (a!37 (ite (= T7 4)
                                           (Build_ArrayoptionHTMLElement
                                             a!36
                                             a!31
                                             a!32
                                             a!33
                                             (SomeHTMLElement U7)
                                             a!35)
                                           (html_body (dc_html (wd_document V7)))))
                                (a!42 (ite (or ((_ is HTMLImage) U7)
                                               ((_ is HTMLScript) U7))
                                           NoneDOMElement
                                           (ite ((_ is HTMLForm) U7)
                                                a!41
                                                NoneDOMElement)))
                                (a!60 (ite (= H7 2)
                                           a!56
                                           (ite (= H7 3)
                                                a!57
                                                (ite (= H7 4) a!58 a!59))))
                                (a!69 (ite ((_ is url_path_data)
                                             (url_path (wd_location D7)))
                                           (SomeOrigin a!68)
                                           NoneOrigin))
                                (a!71 (ite ((_ is url_path_blob)
                                             (url_path (wd_location D7)))
                                           a!70
                                           NoneOrigin))
                                (a!77 (ite ((_ is url_path_data)
                                             (url_path (wd_location Y6)))
                                           (SomeOrigin a!76)
                                           NoneOrigin))
                                (a!79 (ite ((_ is url_path_blob)
                                             (url_path (wd_location Y6)))
                                           a!78
                                           NoneOrigin))
                                (a!86 (ite (= H7 4)
                                           (Build_ArrayoptionDOMElement
                                             a!54
                                             a!55
                                             a!56
                                             a!57
                                             (SomeDOMElement a!85)
                                             a!59)
                                           (dm_body (dc_dom (wd_document M7)))))
                                (a!97 (ite (= B7 4)
                                           (Build_ArrayoptionHTMLElement
                                             a!96
                                             a!91
                                             a!92
                                             a!93
                                             (SomeHTMLElement C7)
                                             a!95)
                                           (html_body (dc_html (wd_document D7)))))
                                (a!102 (ite (or ((_ is HTMLImage) C7)
                                                ((_ is HTMLScript) C7))
                                            NoneDOMElement
                                            (ite ((_ is HTMLForm) C7)
                                                 a!101
                                                 NoneDOMElement)))
                                (a!114 (ite (= K7 1)
                                            (@1ArrayWindow (windows E7))
                                            (ite (= K7 2)
                                                 (@2ArrayWindow (windows E7))
                                                 a!113)))
                                (a!117 (ite (= (frame_window J7) 1)
                                            (@1ArrayWindow (windows E7))
                                            (ite (= (frame_window J7) 2)
                                                 (@2ArrayWindow (windows E7))
                                                 a!116)))
                                (a!126 (ite (= W8 4)
                                            (Build_ArrayoptionInt
                                              a!125
                                              a!120
                                              a!121
                                              a!122
                                              X8
                                              a!124)
                                            (in_body (dc_init (wd_document Y8)))))
                                (a!137 (ite (= L8 2)
                                            a!133
                                            (ite (= L8 3)
                                                 a!134
                                                 (ite (= L8 4) a!135 a!136))))
                                (a!145 (ite (= L8 4)
                                            (Build_ArrayoptionDOMElement
                                              a!131
                                              a!132
                                              a!133
                                              a!134
                                              (SomeDOMElement a!144)
                                              a!136)
                                            (dm_body (dc_dom (wd_document Q8)))))
                                (a!156 (ite (= E8 4)
                                            (Build_ArrayoptionInt
                                              a!155
                                              a!150
                                              a!151
                                              a!152
                                              F8
                                              a!154)
                                            (in_body (dc_init (wd_document G8)))))
                                (a!161 (ite (= O8 1)
                                            (@1ArrayWindow (windows H8))
                                            (ite (= O8 2)
                                                 (@2ArrayWindow (windows H8))
                                                 a!160)))
                                (a!164 (ite (= (frame_window N8) 1)
                                            (@1ArrayWindow (windows H8))
                                            (ite (= (frame_window N8) 2)
                                                 (@2ArrayWindow (windows H8))
                                                 a!163)))
                                (a!173 (ite (= D 2)
                                            a!169
                                            (ite (= D 3)
                                                 a!170
                                                 (ite (= D 4) a!171 a!172))))
                                (a!181 (ite (= (frame_window G) 1)
                                            (@1ArrayWindow (windows L))
                                            (ite (= (frame_window G) 2)
                                                 (@2ArrayWindow (windows L))
                                                 a!180)))
                                (a!191 (ite (= C1 2)
                                            a!187
                                            (ite (= C1 3)
                                                 a!188
                                                 (ite (= C1 4) a!189 a!190))))
                                (a!199 (ite (= (frame_window F1) 1)
                                            (@1ArrayWindow (windows K1))
                                            (ite (= (frame_window F1) 2)
                                                 (@2ArrayWindow (windows K1))
                                                 a!198)))
                                (a!214 (ite (= J4 2)
                                            a!210
                                            (ite (= J4 3)
                                                 a!211
                                                 (ite (= J4 4) a!212 a!213))))
                                (a!222 (ite (= (frame_window L4) 1)
                                            (@1ArrayWindow (windows M4))
                                            (ite (= (frame_window L4) 2)
                                                 (@2ArrayWindow (windows M4))
                                                 a!221)))
                                (a!233 (ite (= C4 2)
                                            a!229
                                            (ite (= C4 3)
                                                 a!230
                                                 (ite (= C4 4) a!231 a!232))))
                                (a!241 (ite (= (frame_window E4) 1)
                                            (@1ArrayWindow (windows S4))
                                            (ite (= (frame_window E4) 2)
                                                 (@2ArrayWindow (windows S4))
                                                 a!240)))
                                (a!246 (or (= (csp_trusted_types Z3)
                                              NoneTrustedTypes)
                                           (and a!245
                                                (= (csp_trusted_types Z3)
                                                   (SomeTrustedTypes Y3)))))
                                (a!255 (ite (= A2 2)
                                            a!251
                                            (ite (= A2 3)
                                                 a!252
                                                 (ite (= A2 4) a!253 a!254))))
                                (a!263 (ite (= (frame_window D2) 1)
                                            (@1ArrayWindow (windows H2))
                                            (ite (= (frame_window D2) 2)
                                                 (@2ArrayWindow (windows H2))
                                                 a!262)))
                                (a!272 (ite (= W2 2)
                                            a!268
                                            (ite (= W2 3)
                                                 a!269
                                                 (ite (= W2 4) a!270 a!271))))
                                (a!280 (ite (= (frame_window Z2) 1)
                                            (@1ArrayWindow (windows E3))
                                            (ite (= (frame_window Z2) 2)
                                                 (@2ArrayWindow (windows E3))
                                                 a!279)))
                                (a!290 (ite (= T3 2)
                                            a!286
                                            (ite (= T3 3)
                                                 a!287
                                                 (ite (= T3 4) a!288 a!289))))
                                (a!299 (or (= (csp_trusted_types L6)
                                              NoneTrustedTypes)
                                           (and a!298
                                                (= (csp_trusted_types L6)
                                                   (SomeTrustedTypes K6)))))
                                (a!307 (ite (= I5 2)
                                            a!303
                                            (ite (= I5 3)
                                                 a!304
                                                 (ite (= I5 4) a!305 a!306))))
                                (a!315 (ite (= (frame_window L5) 1)
                                            (@1ArrayWindow (windows Q5))
                                            (ite (= (frame_window L5) 2)
                                                 (@2ArrayWindow (windows Q5))
                                                 a!314)))
                                (a!325 (ite (= F6 2)
                                            a!321
                                            (ite (= F6 3)
                                                 a!322
                                                 (ite (= F6 4) a!323 a!324)))))
                          (let ((a!9 (ite (= Y 0) a!2 (ite (= Y 1) a!3 a!8)))
                                (a!20 (ite ((_ is url_path_data)
                                             (url_path (wd_location V7)))
                                           NoneOrigin
                                           a!19))
                                (a!28 (ite ((_ is url_path_data)
                                             (url_path (wd_location Q7)))
                                           NoneOrigin
                                           a!27))
                                (a!38 (ite (= T7 2)
                                           (Build_ArrayoptionHTMLElement
                                             a!36
                                             a!31
                                             (SomeHTMLElement U7)
                                             a!33
                                             a!34
                                             a!35)
                                           (ite (= T7 3)
                                                (Build_ArrayoptionHTMLElement
                                                  a!36
                                                  a!31
                                                  a!32
                                                  (SomeHTMLElement U7)
                                                  a!34
                                                  a!35)
                                                a!37)))
                                (a!49 (ite (= T7 4)
                                           (Build_ArrayoptionDOMElement
                                             a!48
                                             a!43
                                             a!44
                                             a!45
                                             a!42
                                             a!47)
                                           (dm_body (dc_dom (wd_document V7)))))
                                (a!61 (ite (= H7 0)
                                           a!54
                                           (ite (= H7 1) a!55 a!60)))
                                (a!72 (ite ((_ is url_path_data)
                                             (url_path (wd_location D7)))
                                           NoneOrigin
                                           a!71))
                                (a!80 (ite ((_ is url_path_data)
                                             (url_path (wd_location Y6)))
                                           NoneOrigin
                                           a!79))
                                (a!87 (ite (= H7 2)
                                           (Build_ArrayoptionDOMElement
                                             a!54
                                             a!55
                                             (SomeDOMElement a!85)
                                             a!57
                                             a!58
                                             a!59)
                                           (ite (= H7 3)
                                                (Build_ArrayoptionDOMElement
                                                  a!54
                                                  a!55
                                                  a!56
                                                  (SomeDOMElement a!85)
                                                  a!58
                                                  a!59)
                                                a!86)))
                                (a!98 (ite (= B7 2)
                                           (Build_ArrayoptionHTMLElement
                                             a!96
                                             a!91
                                             (SomeHTMLElement C7)
                                             a!93
                                             a!94
                                             a!95)
                                           (ite (= B7 3)
                                                (Build_ArrayoptionHTMLElement
                                                  a!96
                                                  a!91
                                                  a!92
                                                  (SomeHTMLElement C7)
                                                  a!94
                                                  a!95)
                                                a!97)))
                                (a!109 (ite (= B7 4)
                                            (Build_ArrayoptionDOMElement
                                              a!108
                                              a!103
                                              a!104
                                              a!105
                                              a!102
                                              a!107)
                                            (dm_body (dc_dom (wd_document D7)))))
                                (a!115 (= (ite (= K7 0)
                                               (@0ArrayWindow (windows E7))
                                               a!114)
                                          L7))
                                (a!118 (= (ite (= (frame_window J7) 0)
                                               (@0ArrayWindow (windows E7))
                                               a!117)
                                          I7))
                                (a!127 (ite (= W8 1)
                                            (Build_ArrayoptionInt
                                              a!125
                                              X8
                                              a!121
                                              a!122
                                              a!123
                                              a!124)
                                            (ite (= W8 2)
                                                 (Build_ArrayoptionInt
                                                   a!125
                                                   a!120
                                                   X8
                                                   a!122
                                                   a!123
                                                   a!124)
                                                 (ite (= W8 3)
                                                      (Build_ArrayoptionInt
                                                        a!125
                                                        a!120
                                                        a!121
                                                        X8
                                                        a!123
                                                        a!124)
                                                      a!126))))
                                (a!138 (ite (= L8 0)
                                            a!131
                                            (ite (= L8 1) a!132 a!137)))
                                (a!146 (ite (= L8 2)
                                            (Build_ArrayoptionDOMElement
                                              a!131
                                              a!132
                                              (SomeDOMElement a!144)
                                              a!134
                                              a!135
                                              a!136)
                                            (ite (= L8 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!131
                                                   a!132
                                                   a!133
                                                   (SomeDOMElement a!144)
                                                   a!135
                                                   a!136)
                                                 a!145)))
                                (a!157 (ite (= E8 1)
                                            (Build_ArrayoptionInt
                                              a!155
                                              F8
                                              a!151
                                              a!152
                                              a!153
                                              a!154)
                                            (ite (= E8 2)
                                                 (Build_ArrayoptionInt
                                                   a!155
                                                   a!150
                                                   F8
                                                   a!152
                                                   a!153
                                                   a!154)
                                                 (ite (= E8 3)
                                                      (Build_ArrayoptionInt
                                                        a!155
                                                        a!150
                                                        a!151
                                                        F8
                                                        a!153
                                                        a!154)
                                                      a!156))))
                                (a!162 (= (ite (= O8 0)
                                               (@0ArrayWindow (windows H8))
                                               a!161)
                                          I8))
                                (a!165 (= (ite (= (frame_window N8) 0)
                                               (@0ArrayWindow (windows H8))
                                               a!164)
                                          M8))
                                (a!174 (ite (= D 0)
                                            a!167
                                            (ite (= D 1) a!168 a!173)))
                                (a!182 (= (ite (= (frame_window G) 0)
                                               (@0ArrayWindow (windows L))
                                               a!181)
                                          J))
                                (a!192 (ite (= C1 0)
                                            a!185
                                            (ite (= C1 1) a!186 a!191)))
                                (a!200 (= (ite (= (frame_window F1) 0)
                                               (@0ArrayWindow (windows K1))
                                               a!199)
                                          I1))
                                (a!215 (ite (= J4 0)
                                            a!208
                                            (ite (= J4 1) a!209 a!214)))
                                (a!223 (= (ite (= (frame_window L4) 0)
                                               (@0ArrayWindow (windows M4))
                                               a!222)
                                          N4))
                                (a!234 (ite (= C4 0)
                                            a!227
                                            (ite (= C4 1) a!228 a!233)))
                                (a!242 (= (ite (= (frame_window E4) 0)
                                               (@0ArrayWindow (windows S4))
                                               a!241)
                                          R4))
                                (a!256 (ite (= A2 0)
                                            a!249
                                            (ite (= A2 1) a!250 a!255)))
                                (a!264 (= (ite (= (frame_window D2) 0)
                                               (@0ArrayWindow (windows H2))
                                               a!263)
                                          G2))
                                (a!273 (ite (= W2 0)
                                            a!266
                                            (ite (= W2 1) a!267 a!272)))
                                (a!281 (= (ite (= (frame_window Z2) 0)
                                               (@0ArrayWindow (windows E3))
                                               a!280)
                                          C3))
                                (a!291 (ite (= T3 0)
                                            a!284
                                            (ite (= T3 1) a!285 a!290)))
                                (a!308 (ite (= I5 0)
                                            a!301
                                            (ite (= I5 1) a!302 a!307)))
                                (a!316 (= (ite (= (frame_window L5) 0)
                                               (@0ArrayWindow (windows Q5))
                                               a!315)
                                          O5))
                                (a!326 (ite (= F6 0)
                                            a!319
                                            (ite (= F6 1) a!320 a!325))))
                          (let ((a!10 (= (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!9)))
                                         A1))
                                (a!11 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!9)))))
                                (a!12 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!9)))))
                                (a!21 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location V7)))
                                           a!17
                                           a!20))
                                (a!29 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location Q7)))
                                           a!25
                                           a!28))
                                (a!39 (ite (= T7 0)
                                           (Build_ArrayoptionHTMLElement
                                             (SomeHTMLElement U7)
                                             a!31
                                             a!32
                                             a!33
                                             a!34
                                             a!35)
                                           (ite (= T7 1)
                                                (Build_ArrayoptionHTMLElement
                                                  a!36
                                                  (SomeHTMLElement U7)
                                                  a!32
                                                  a!33
                                                  a!34
                                                  a!35)
                                                a!38)))
                                (a!50 (ite (= T7 1)
                                           (Build_ArrayoptionDOMElement
                                             a!48
                                             a!42
                                             a!44
                                             a!45
                                             a!46
                                             a!47)
                                           (ite (= T7 2)
                                                (Build_ArrayoptionDOMElement
                                                  a!48
                                                  a!43
                                                  a!42
                                                  a!45
                                                  a!46
                                                  a!47)
                                                (ite (= T7 3)
                                                     (Build_ArrayoptionDOMElement
                                                       a!48
                                                       a!43
                                                       a!44
                                                       a!42
                                                       a!46
                                                       a!47)
                                                     a!49))))
                                (a!62 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!61)))
                                         J7))
                                (a!63 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!61)))
                                         R6))
                                (a!64 (not ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!61)))))
                                (a!73 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location D7)))
                                           a!69
                                           a!72))
                                (a!81 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location Y6)))
                                           a!77
                                           a!80))
                                (a!83 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!61)))))
                                (a!84 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!61)))))
                                (a!88 (ite (= H7 0)
                                           (Build_ArrayoptionDOMElement
                                             (SomeDOMElement a!85)
                                             a!55
                                             a!56
                                             a!57
                                             a!58
                                             a!59)
                                           (ite (= H7 1)
                                                (Build_ArrayoptionDOMElement
                                                  a!54
                                                  (SomeDOMElement a!85)
                                                  a!56
                                                  a!57
                                                  a!58
                                                  a!59)
                                                a!87)))
                                (a!99 (ite (= B7 0)
                                           (Build_ArrayoptionHTMLElement
                                             (SomeHTMLElement C7)
                                             a!91
                                             a!92
                                             a!93
                                             a!94
                                             a!95)
                                           (ite (= B7 1)
                                                (Build_ArrayoptionHTMLElement
                                                  a!96
                                                  (SomeHTMLElement C7)
                                                  a!92
                                                  a!93
                                                  a!94
                                                  a!95)
                                                a!98)))
                                (a!110 (ite (= B7 1)
                                            (Build_ArrayoptionDOMElement
                                              a!108
                                              a!102
                                              a!104
                                              a!105
                                              a!106
                                              a!107)
                                            (ite (= B7 2)
                                                 (Build_ArrayoptionDOMElement
                                                   a!108
                                                   a!103
                                                   a!102
                                                   a!105
                                                   a!106
                                                   a!107)
                                                 (ite (= B7 3)
                                                      (Build_ArrayoptionDOMElement
                                                        a!108
                                                        a!103
                                                        a!104
                                                        a!102
                                                        a!106
                                                        a!107)
                                                      a!109))))
                                (a!128 (Build_Initiators (in_toplevel (dc_init (wd_document Y8)))
                                                         (ite (= W8 0)
                                                              (Build_ArrayoptionInt
                                                                X8
                                                                a!120
                                                                a!121
                                                                a!122
                                                                a!123
                                                                a!124)
                                                              a!127)))
                                (a!139 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!138)))
                                          N8))
                                (a!140 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!138)))
                                          P8))
                                (a!141 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!138)))))
                                (a!142 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!138)))))
                                (a!143 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!138)))))
                                (a!147 (ite (= L8 0)
                                            (Build_ArrayoptionDOMElement
                                              (SomeDOMElement a!144)
                                              a!132
                                              a!133
                                              a!134
                                              a!135
                                              a!136)
                                            (ite (= L8 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!131
                                                   (SomeDOMElement a!144)
                                                   a!133
                                                   a!134
                                                   a!135
                                                   a!136)
                                                 a!146)))
                                (a!158 (Build_Initiators (in_toplevel (dc_init (wd_document G8)))
                                                         (ite (= E8 0)
                                                              (Build_ArrayoptionInt
                                                                F8
                                                                a!150
                                                                a!151
                                                                a!152
                                                                a!153
                                                                a!154)
                                                              a!157)))
                                (a!175 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!174)))
                                          G))
                                (a!176 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!174)))
                                          F))
                                (a!177 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!174)))))
                                (a!178 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!174)))))
                                (a!179 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!174)))))
                                (a!193 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!192)))
                                          F1))
                                (a!194 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!192)))
                                          E1))
                                (a!195 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!192)))))
                                (a!196 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!192)))))
                                (a!197 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!192)))))
                                (a!216 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!215)))
                                          L4))
                                (a!217 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!215)))
                                          K4))
                                (a!218 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!215)))))
                                (a!219 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!215)))))
                                (a!220 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!215)))))
                                (a!235 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!234)))
                                          E4))
                                (a!236 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!234)))
                                          D4))
                                (a!237 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!234)))))
                                (a!238 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!234)))))
                                (a!239 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!234)))))
                                (a!257 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!256)))
                                          D2))
                                (a!258 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!256)))
                                          C2))
                                (a!259 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!256)))))
                                (a!260 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!256)))))
                                (a!261 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!256)))))
                                (a!274 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!273)))
                                          Z2))
                                (a!275 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!273)))
                                          Y2))
                                (a!276 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!273)))))
                                (a!277 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!273)))))
                                (a!278 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!273)))))
                                (a!292 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!291)))))
                                (a!293 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!291)))))
                                (a!294 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!291)))
                                          V3))
                                (a!309 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!308)))
                                          L5))
                                (a!310 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!308)))
                                          K5))
                                (a!311 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!308)))))
                                (a!312 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!308)))))
                                (a!313 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!308)))))
                                (a!327 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!326)))))
                                (a!328 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!326)))))
                                (a!329 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!326)))
                                          H6)))
                          (let ((a!30 (and (not (= (ite a!14 a!15 a!21)
                                                   NoneOrigin))
                                           (= (ite a!14 a!15 a!21)
                                              (ite a!22 a!23 a!29))
                                           (not ((_ is SomeDomain)
                                                  (wd_document_domain Q7)))))
                                (a!40 (Build_HTML (html_nonce (dc_html (wd_document V7)))
                                                  (html_head (dc_html (wd_document V7)))
                                                  a!39))
                                (a!51 (Build_DOM (dm_nonce (dc_dom (wd_document V7)))
                                                 (dm_head (dc_dom (wd_document V7)))
                                                 (ite (= T7 0)
                                                      (Build_ArrayoptionDOMElement
                                                        a!42
                                                        a!43
                                                        a!44
                                                        a!45
                                                        a!46
                                                        a!47)
                                                      a!50)))
                                (a!82 (and (not (= (ite a!66 a!67 a!73)
                                                   NoneOrigin))
                                           (= (ite a!66 a!67 a!73)
                                              (ite a!74 a!75 a!81))
                                           (not ((_ is SomeDomain)
                                                  (wd_document_domain Y6)))))
                                (a!89 (Build_DOM (dm_nonce (dc_dom (wd_document M7)))
                                                 (dm_head (dc_dom (wd_document M7)))
                                                 a!88))
                                (a!100 (Build_HTML (html_nonce (dc_html (wd_document D7)))
                                                   (html_head (dc_html (wd_document D7)))
                                                   a!99))
                                (a!111 (Build_DOM (dm_nonce (dc_dom (wd_document D7)))
                                                  (dm_head (dc_dom (wd_document D7)))
                                                  (ite (= B7 0)
                                                       (Build_ArrayoptionDOMElement
                                                         a!102
                                                         a!103
                                                         a!104
                                                         a!105
                                                         a!106
                                                         a!107)
                                                       a!110)))
                                (a!129 (Build_Window (wd_nonce Y8)
                                                     (wd_parent Y8)
                                                     (wd_location Y8)
                                                     (wd_document_domain Y8)
                                                     (Build_Document (dc_version (wd_document Y8))
                                                                     (dc_nonce (wd_document Y8))
                                                                     (dc_headers (wd_document Y8))
                                                                     (dc_html (wd_document Y8))
                                                                     (dc_dom (wd_document Y8))
                                                                     a!128)))
                                (a!148 (Build_DOM (dm_nonce (dc_dom (wd_document Q8)))
                                                  (dm_head (dc_dom (wd_document Q8)))
                                                  a!147))
                                (a!159 (Build_Window (wd_nonce G8)
                                                     (wd_parent G8)
                                                     (wd_location G8)
                                                     (wd_document_domain G8)
                                                     (Build_Document (dc_version (wd_document G8))
                                                                     (dc_nonce (wd_document G8))
                                                                     (dc_headers (wd_document G8))
                                                                     (dc_html (wd_document G8))
                                                                     (dc_dom (wd_document G8))
                                                                     a!158)))
                                (a!183 (and a!175
                                            a!176
                                            a!177
                                            a!178
                                            a!179
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!174)))
                                            ((_ is SomeDOMElement) a!174)
                                            (= R1 E)
                                            (= Z K)
                                            (= P Q)
                                            (= K P)
                                            (= J Q)
                                            a!182
                                            (= W C)
                                            (= N (DOMPath H I))
                                            (= N (DOMPath nilInt O))
                                            (= C (DOMPath (consInt D H) I))
                                            (= T1 L)
                                            (= L M)))
                                (a!201 (and a!193
                                            a!194
                                            a!195
                                            a!196
                                            a!197
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!192)))
                                            ((_ is SomeDOMElement) a!192)
                                            (= R1 D1)
                                            (= I1 P1)
                                            (= S1 J1)
                                            (= O1 P1)
                                            (= J1 O1)
                                            a!200
                                            (= Q1 B1)
                                            (= M1 (DOMPath G1 H1))
                                            (= M1 (DOMPath nilInt N1))
                                            (= B1 (DOMPath (consInt C1 G1) H1))
                                            (= T1 K1)
                                            (= K1 L1)))
                                (a!225 (and a!216
                                            a!217
                                            a!218
                                            a!219
                                            a!220
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!215)))
                                            ((_ is SomeDOMElement) a!215)
                                            (= R4 O4)
                                            a!223
                                            (= G4 (DOMPath P4 Q4))
                                            (= G4 (DOMPath (consInt J4 H4) I4))
                                            (= S4 M4)
                                            a!224))
                                (a!265 (and a!257
                                            a!258
                                            a!259
                                            a!260
                                            a!261
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!256)))
                                            ((_ is SomeDOMElement) a!256)
                                            (= R1 B2)
                                            (= G2 L2)
                                            a!264
                                            (= J2 (DOMPath E2 F2))
                                            (= J2 (DOMPath nilInt K2))
                                            (= Z1 (DOMPath (consInt A2 E2) F2))
                                            (= Q1 Z1)
                                            (= H2 I2)
                                            (= T1 H2)
                                            (= (url_protocol (wd_location L2))
                                               ProtocolHTTPS)
                                            (= (url_protocol (wd_location B2))
                                               ProtocolHTTPS)))
                                (a!282 (and a!274
                                            a!275
                                            a!276
                                            a!277
                                            a!278
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!273)))
                                            ((_ is SomeDOMElement) a!273)
                                            (= I3 J3)
                                            (= D3 I3)
                                            (= C3 J3)
                                            (= U3 D3)
                                            (= K3 X2)
                                            a!281
                                            (= G3 (DOMPath A3 B3))
                                            (= G3 (DOMPath nilInt H3))
                                            (= R3 V2)
                                            (= V2 (DOMPath (consInt W2 A3) B3))
                                            (= E3 F3)
                                            (= L3 E3)))
                                (a!317 (and a!309
                                            a!310
                                            a!311
                                            a!312
                                            a!313
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!308)))
                                            ((_ is SomeDOMElement) a!308)
                                            (= W5 J5)
                                            (= G6 P5)
                                            (= P5 U5)
                                            (= O5 V5)
                                            (= U5 V5)
                                            a!316
                                            (= D6 H5)
                                            (= S5 (DOMPath M5 N5))
                                            (= S5 (DOMPath nilInt T5))
                                            (= H5 (DOMPath (consInt I5 M5) N5))
                                            (= X5 Q5)
                                            (= Q5 R5))))
                          (let ((a!52 (Build_Window (wd_nonce V7)
                                                    (wd_parent V7)
                                                    (wd_location V7)
                                                    (wd_document_domain V7)
                                                    (Build_Document (+ 1 S7)
                                                                    (dc_nonce (wd_document V7))
                                                                    (dc_headers (wd_document V7))
                                                                    a!40
                                                                    a!51
                                                                    (dc_init (wd_document V7)))))
                                (a!90 (Build_Window (wd_nonce M7)
                                                    (wd_parent M7)
                                                    (wd_location M7)
                                                    (wd_document_domain M7)
                                                    (Build_Document (+ 1 G7)
                                                                    (dc_nonce (wd_document M7))
                                                                    (dc_headers (wd_document M7))
                                                                    (dc_html (wd_document M7))
                                                                    a!89
                                                                    (dc_init (wd_document M7)))))
                                (a!112 (Build_Window (wd_nonce D7)
                                                     (wd_parent D7)
                                                     (wd_location D7)
                                                     (wd_document_domain D7)
                                                     (Build_Document (+ 1 A7)
                                                                     (dc_nonce (wd_document D7))
                                                                     (dc_headers (wd_document D7))
                                                                     a!100
                                                                     a!111
                                                                     (dc_init (wd_document D7)))))
                                (a!130 (and (= A9 S8)
                                            (= D9 V8)
                                            (= R8 Y8)
                                            (= V8 a!129)
                                            (= U8
                                               (DOMPath nilInt (DOMIndex W8)))
                                            (= Q1 U8)
                                            (= T1 T8)
                                            (= X8 NoneInt)))
                                (a!149 (Build_Window (wd_nonce Q8)
                                                     (wd_parent Q8)
                                                     (wd_location Q8)
                                                     (wd_document_domain Q8)
                                                     (Build_Document (+ 1 K8)
                                                                     (dc_nonce (wd_document Q8))
                                                                     (dc_headers (wd_document Q8))
                                                                     (dc_html (wd_document Q8))
                                                                     a!148
                                                                     (dc_init (wd_document Q8)))))
                                (a!184 (or (and (= R1 V)
                                                (= Z U)
                                                (= U V)
                                                (= W S)
                                                (= S (DOMPath nilInt T))
                                                (= T1 R))
                                           a!183))
                                (a!202 (or (and (= R1 Y1)
                                                (= X1 Y1)
                                                (= S1 X1)
                                                (= V1 (DOMPath nilInt W1))
                                                (= Q1 V1)
                                                (= T1 U1))
                                           a!201))
                                (a!226 (or a!206
                                           (and (= R4 W4)
                                                (= U4 (DOMPath P4 Q4))
                                                (= U4 (DOMPath nilInt V4))
                                                (= S4 T4)
                                                a!207)
                                           a!225))
                                (a!283 (or (and (= U3 P3)
                                                (= P3 Q3)
                                                (= K3 Q3)
                                                (= R3 N3)
                                                (= N3 (DOMPath nilInt O3))
                                                (= L3 M3))
                                           a!282))
                                (a!318 (or (and (= B6 C6)
                                                (= W5 C6)
                                                (= G6 B6)
                                                (= D6 Z5)
                                                (= Z5 (DOMPath nilInt A6))
                                                (= X5 Y5))
                                           a!317)))
                          (let ((a!53 (and (= A9 S7)
                                           (ite ((_ is SomeDomain)
                                                  (wd_document_domain V7))
                                                a!13
                                                a!30)
                                           (= R8 R7)
                                           (= R7 a!52)
                                           (= R1 V7)
                                           (= Z Q7)
                                           (= P7 (DOMPath nilInt (DOMIndex T7)))
                                           (= Q1 P7)
                                           (= T1 O7)
                                           (= N7 U7)))
                                (a!119 (and (= A9 G7)
                                            (= G7 A7)
                                            a!62
                                            a!63
                                            a!64
                                            (ite ((_ is SomeDomain)
                                                   (wd_document_domain D7))
                                                 a!65
                                                 a!82)
                                            a!83
                                            a!84
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!61)))
                                            ((_ is SomeDOMElement) a!61)
                                            (= R8 F7)
                                            (= L7 Z6)
                                            (= F7 a!90)
                                            (= Z6 a!112)
                                            (= I7 D7)
                                            (= R1 M7)
                                            (= V6 Y6)
                                            (= Z V6)
                                            a!115
                                            a!118
                                            (= X6 (DOMPath S6 T6))
                                            (= X6
                                               (DOMPath nilInt (DOMIndex B7)))
                                            (= Q6 (DOMPath (consInt H7 S6) T6))
                                            (= Q1 Q6)
                                            (= E7 W6)
                                            (= T1 E7)
                                            (= N7 U6)
                                            (= U6 C7)))
                                (a!166 (and (= A9 K8)
                                            (= K8 A8)
                                            a!139
                                            a!140
                                            a!141
                                            a!142
                                            a!143
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!138)))
                                            ((_ is SomeDOMElement) a!138)
                                            (= D9 J8)
                                            (= R8 Q8)
                                            (= J8 a!149)
                                            (= M8 G8)
                                            (= I8 D8)
                                            (= D8 a!159)
                                            a!162
                                            a!165
                                            (= C8 (DOMPath X7 Y7))
                                            (= C8
                                               (DOMPath nilInt (DOMIndex E8)))
                                            (= W7 (DOMPath (consInt L8 X7) Y7))
                                            (= Q1 W7)
                                            (= H8 B8)
                                            (= T1 H8)
                                            (= Z7 F8)
                                            (= Z7 NoneInt)))
                                (a!243 (and a!226
                                            a!235
                                            a!236
                                            a!237
                                            a!238
                                            a!239
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!234)))
                                            ((_ is SomeDOMElement) a!234)
                                            (= R1 F4)
                                            a!242
                                            (= B4 (DOMPath (consInt C4 P4) Q4))
                                            (= Q1 B4)
                                            (= T1 S4)))
                                (a!295 (and (or a!244 (and a!246 a!247))
                                            (or a!248 a!265)
                                            a!283
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!291)))
                                            a!292
                                            a!293
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!291)))
                                            ((_ is SomeDOMElement) a!291)
                                            (= P6 A4)
                                            (= A4 U3)
                                            (= K3 (st_window T2))
                                            (= R2 V3)
                                            (= A1 R2)
                                            a!294
                                            (= R3 (DOMPath S3 (DOMIndex T3)))
                                            (= S2 R3)
                                            (= U2 L3)
                                            (= T1 U2)
                                            (= N7 Q2)
                                            (= C5 T2)))
                                (a!330 (and (or a!297 (and a!299 a!300))
                                            a!318
                                            (not (c_restrict_tt_to_secure_contexts
                                                   (config T1)))
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!326)))
                                            a!327
                                            a!328
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!326)))
                                            ((_ is SomeDOMElement) a!326)
                                            (= P6 M6)
                                            (= W5 (st_window F5))
                                            (= M6 G6)
                                            (= D5 H6)
                                            (= A1 D5)
                                            a!329
                                            (= E5 D6)
                                            (= D6 (DOMPath E6 (DOMIndex F6)))
                                            (= G5 X5)
                                            (= T1 G5)
                                            (= N7 B5)
                                            (= C5 F5))))
                          (let ((a!296 (or (and (= R1 A5)
                                                (= Y4 (DOMPath nilInt Z4))
                                                (= Q1 Y4)
                                                (= T1 X4)
                                                a!205)
                                           a!243
                                           a!295)))
                          (let ((a!331 (or (and a!296
                                                (c_restrict_tt_to_secure_contexts
                                                  (config T1)))
                                           a!330)))
                          (let ((a!332 (and (or (not (tt_require_for_script N6))
                                                (and a!331
                                                     (tt_require_for_script N6)))
                                            (= (csp_trusted_types O6)
                                               (SomeTrustedTypes N6)))))
                          (let ((a!334 (and (or (= (csp_trusted_types O6)
                                                   NoneTrustedTypes)
                                                a!332)
                                            a!333)))
                          (let ((a!335 (and (Reachable T1 Z8 C5)
                                            (= A a!1)
                                            (= C5
                                               (Build_State A9
                                                            B9
                                                            C9
                                                            R1
                                                            E9
                                                            F9
                                                            G9))
                                            (= W (DOMPath X (DOMIndex Y)))
                                            a!10
                                            ((_ is SomeDOMElement) a!9)
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!9)))
                                            a!11
                                            a!12
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!9)))
                                            (or a!53 a!119)
                                            (or a!130 a!166)
                                            a!184
                                            a!202
                                            a!203
                                            (or a!204 a!334)
                                            (= B
                                               (consEvent (EvScriptUpdateHTML
                                                            W
                                                            Q1
                                                            S1)
                                                          Z8)))))
                            (=> a!335 (Reachable T1 B A))))))))))))))
                          :weight 0))))
      (a!4 (Build_URL ProtocolHTTPS
                      (SomeDomain (domain 3143))
                      (SomeInt 34522)
                      (url_path_res (anypath 212))))
      (a!5 (Build_RequestHeaders
             NoneOrigin
             (Build_ArrayoptionCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping)
             NoneURL))
      (a!6 (Build_URL ProtocolHTTPS
                      (SomeDomain (domain 3143))
                      (SomeInt 34522)
                      (url_path_res (anypath 8214))))
      (a!7 (Build_ArrayoptionCookieMapping
             NoneCookieMapping
             NoneCookieMapping
             NoneCookieMapping
             (SomeCookieMapping (Build_CookieMapping (Secure 76081) 8213))
             NoneCookieMapping
             NoneCookieMapping))
      (a!8 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 19153 19154))
                      (SomeInt 34826)
                      (url_path_res (anypath 76072))))
      (a!10 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 27503))
                                true)))
      (a!12 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 76116
                            76115
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!14 (SomeSetCookie (Build_SetCookie (NoPrefix 76114)
                                            19152
                                            (SomeDomain (subdomain 19153 19154))
                                            (subdomain 19153 19154)
                                            (anypath 76113)
                                            false
                                            false
                                            SSStrict)))
      (a!15 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                (SomeTrustedTypes (Build_TrustedTypes
                                                    NoneoptionInt
                                                    false)))))
      (a!18 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 76109)
                                              76108
                                              NoneDomain
                                              (domain 76107)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 76106))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 27542)
                                  (url_path_data 76105 76104)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!19 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 76103
                            76102
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!21 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 34339))
                                false)))
      (a!24 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 49941)
                                                  (url_path_data 76074 76073)))))
      (a!25 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 49939)
                                                  (url_path_data 76071 76070)))))
      (a!26 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 49938)
                                                  (url_path_data 76069 76068)))))
      (a!27 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 49937)
                                                  (url_path_data 76067 76066)))))
      (a!30 (SomeSetCookie (Build_SetCookie (Secure 76081)
                                            8213
                                            (SomeDomain (domain 3143))
                                            (domain 3143)
                                            (anypath 8214)
                                            true
                                            false
                                            SSStrict)))
      (a!31 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                      (SomeoptionInt (SomeInt 27998))
                                      13861
                                      NoneInt
                                      NonePath)))
      (a!34 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 28533)
                                                   (url_path_data 76078 76077)))))
      (a!35 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 61136)
                                                  (url_path_data 76065 76064)))))
      (a!36 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 28534)
                                                   (url_path_data 76076 76075)))))
      (a!37 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 61134)
                                                  (url_path_data 76063 76062)))))
      (a!38 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 61133)
                                                  (url_path_data 76061 76060)))))
      (a!40 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 76098)
                                              76097
                                              NoneDomain
                                              (domain 76096)
                                              slash
                                              false
                                              false
                                              SSStrict))
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 27541)
                                  (url_path_data 76095 76094)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!41 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 76093
                            76092
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!44 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 26105)
                                                    (url_path_data 76091 76090))
                                         76089)))
      (a!45 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 26032)
                                                    (url_path_data 76088 76087))
                                         76086)))
      (a!46 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 26260)
                                                    (url_path_data 76085 76084))
                                         76083)))
      (a!47 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 49941)
                                                   (url_path_data 76074 76073)))))
      (a!49 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 49939)
                                                   (url_path_data 76071 76070)))))
      (a!50 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 49938)
                                                   (url_path_data 76069 76068)))))
      (a!51 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 49937)
                                                   (url_path_data 76067 76066)))))
      (a!53 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 61136)
                                                   (url_path_data 76065 76064)))))
      (a!54 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 61134)
                                                   (url_path_data 76063 76062)))))
      (a!55 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 61133)
                                                   (url_path_data 76061 76060)))))
      (a!60 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 25615)
                                                   (url_path_data 76056 76055)))))
      (a!63 (Build_Document 23984
                            23985
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 23980
                                        23981
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 23982
                                       23983
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 35771)
                                              (Build_ArrayoptionInt
                                                (SomeInt 35777)
                                                (SomeInt 35776)
                                                (SomeInt 35775)
                                                (SomeInt 35774)
                                                (SomeInt 35773)
                                                (SomeInt 35772)))))
      (a!65 (Build_ArrayContentElement
              (ContentElementHTML
                (Build_HTML 76052
                            76051
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 76050
                            76049
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 76048
                            76047
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 76046
                            76045
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 76044
                            76043
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 76042
                            76041
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!66 (pairOriginoptionCSP
              (TupleOrigin ProtocolHTTP (SomeDomain (domain 0)) (SomeInt 0))
              NoneCSP))
      (a!74 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 4))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 3))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 18951) 1))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!79 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 34825)
                                                  (url_path_data 94421 94420)))))
      (a!81 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34825)
                                                   (url_path_data 94421 94420)))))
      (a!85 (asserted (forall ((A State)
                               (B State)
                               (C listEvent)
                               (D Int)
                               (E Origin)
                               (F Origin)
                               (G optionCSP)
                               (H NestedDOMPath)
                               (I Window)
                               (J listInt)
                               (K DOMSelector)
                               (L ArrayoptionBlob)
                               (M FetchEngine)
                               (N NestedDOMPath)
                               (O ArrayoptionBlob)
                               (P Global)
                               (Q Int)
                               (R FetchEngine)
                               (S Window)
                               (T Int)
                               (U DOMSelector)
                               (V Response)
                               (W Window)
                               (X Global)
                               (Y Window)
                               (Z Window)
                               (A1 Int)
                               (B1 Int)
                               (C1 Response)
                               (D1 Frame)
                               (E1 Int)
                               (F1 HTML)
                               (G1 Window)
                               (H1 Window)
                               (I1 Response)
                               (J1 NestedDOMPath)
                               (K1 ArrayoptionBlob)
                               (L1 Global)
                               (M1 Int)
                               (N1 FetchEngine)
                               (O1 Window)
                               (P1 Int)
                               (Q1 DOMSelector)
                               (R1 Response)
                               (S1 Window)
                               (T1 listInt)
                               (U1 DOMSelector)
                               (V1 Int)
                               (W1 ArrayoptionBlob)
                               (X1 Global)
                               (Y1 NestedDOMPath)
                               (Z1 listEvent)
                               (A2 Int)
                               (B2 FetchEngine)
                               (C2 ServiceWorker)
                               (D2 Window)
                               (E2 ArrayoptionSetCookie)
                               (F2 ArrayoptionBlob)
                               (G2 ArrayoptionStorageItem))
                        (! (let ((a!1 (Build_State (+ 1 A2) B2 C2 D2 E2 F2 G2))
                                 (a!2 (not ((_ is SomeURL)
                                             (rp_hd_location (rp_headers R1)))))
                                 (a!4 (ite ((_ is EmitterScript)
                                             (ft_emitter N1))
                                           (not (= Q1 DOMTopLevel))
                                           (and ((_ is EmitterForm)
                                                  (ft_emitter N1))
                                                (= Q1 DOMTopLevel))))
                                 (a!5 (not ((_ is SomeContentType)
                                             (rp_hd_content_type
                                               (rp_headers R1)))))
                                 (a!6 (image_src (@0ContentElementImage
                                                   (@0SomeContentElement
                                                     (rp_content R1)))))
                                 (a!7 (script_src (@0ContentElementScript
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                 (a!8 (frame_src (@0ContentElementFrame
                                                   (@0SomeContentElement
                                                     (rp_content R1)))))
                                 (a!12 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeScript
                                            ContentTypeHTML))
                                 (a!17 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url R1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url R1)))
                                           (= (rp_hd_csp (rp_headers R1))
                                              NoneCSP)))
                                 (a!18 (html_body (@0ContentElementHTML
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                 (a!40 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document S1)))))
                                 (a!41 ((_ is SomeCSP)
                                         (rp_hd_csp (dc_headers (wd_document S1)))))
                                 (a!42 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location S1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location S1)))))
                                 (a!43 (SomeOrigin (TupleOrigin (url_protocol (wd_location S1))
                                                                (url_host (wd_location S1))
                                                                (url_port (wd_location S1)))))
                                 (a!44 (OpaqueOrigin (@0url_path_data (url_path (wd_location S1)))))
                                 (a!46 (SomeOrigin (@0url_path_blob (url_path (wd_location S1)))))
                                 (a!77 (script_nonce (@0ContentElementScript
                                                       (@0SomeContentElement
                                                         (rp_content R1)))))
                                 (a!78 (@0ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!79 (@1ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!80 (@2ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!81 (@3ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!82 (@4ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!83 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document S1)))))
                                 (a!91 (= (rp_hd_csp (rp_headers R1))
                                          (rp_hd_csp (dc_headers (wd_document O1)))))
                                 (a!93 (= (@1url_path_blob (url_path (rp_url R1)))
                                          0))
                                 (a!94 (= (@1url_path_blob (url_path (rp_url R1)))
                                          1))
                                 (a!95 (= (@1url_path_blob (url_path (rp_url R1)))
                                          2))
                                 (a!96 (= (@1url_path_blob (url_path (rp_url R1)))
                                          3))
                                 (a!97 (= (@1url_path_blob (url_path (rp_url R1)))
                                          4))
                                 (a!105 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content R1)))))
                                 (a!108 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content R1)))))
                                 (a!132 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!133 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!134 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!135 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!136 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!137 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!143 (not ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content R1)))))
                                 (a!144 (SomeDOMElement (DOMElementResource
                                                          (rp_url R1)
                                                          (@0SomeContentElement
                                                            (rp_content R1)))))
                                 (a!145 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!146 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!147 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!148 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!149 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!150 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!157 (ite (= M1 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= M1 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!160 (not (= (rp_hd_content_type
                                                  (rp_headers R1))
                                                NoneContentType)))
                                 (a!162 (not ((_ is SomeURL)
                                               (rp_hd_location (rp_headers V)))))
                                 (a!164 (ite ((_ is EmitterScript)
                                               (ft_emitter R))
                                             (not (= U DOMTopLevel))
                                             (and ((_ is EmitterForm)
                                                    (ft_emitter R))
                                                  (= U DOMTopLevel))))
                                 (a!165 (not ((_ is SomeContentType)
                                               (rp_hd_content_type
                                                 (rp_headers V)))))
                                 (a!166 (image_src (@0ContentElementImage
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!167 (script_src (@0ContentElementScript
                                                      (@0SomeContentElement
                                                        (rp_content V)))))
                                 (a!168 (frame_src (@0ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!172 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeScript
                                             ContentTypeHTML))
                                 (a!177 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!178 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!179 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!180 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!181 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!182 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!188 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url V)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url V)))
                                            (= (rp_hd_csp (rp_headers V))
                                               NoneCSP)))
                                 (a!189 (html_body (@0ContentElementHTML
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!211 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document W)))))
                                 (a!212 ((_ is SomeCSP)
                                          (rp_hd_csp (dc_headers (wd_document W)))))
                                 (a!213 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location W)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location W)))))
                                 (a!214 (SomeOrigin (TupleOrigin (url_protocol (wd_location W))
                                                                 (url_host (wd_location W))
                                                                 (url_port (wd_location W)))))
                                 (a!215 (OpaqueOrigin (@0url_path_data (url_path (wd_location W)))))
                                 (a!217 (SomeOrigin (@0url_path_blob (url_path (wd_location W)))))
                                 (a!248 (script_nonce (@0ContentElementScript
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!249 (@0ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!250 (@1ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!251 (@2ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!252 (@3ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!253 (@4ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!254 (@defaultArrayoptionInt
                                          (in_body (dc_init (wd_document W)))))
                                 (a!262 (= (rp_hd_csp (rp_headers V))
                                           (rp_hd_csp (dc_headers (wd_document S)))))
                                 (a!264 (= (@1url_path_blob (url_path (rp_url V)))
                                           0))
                                 (a!265 (= (@1url_path_blob (url_path (rp_url V)))
                                           1))
                                 (a!266 (= (@1url_path_blob (url_path (rp_url V)))
                                           2))
                                 (a!267 (= (@1url_path_blob (url_path (rp_url V)))
                                           3))
                                 (a!268 (= (@1url_path_blob (url_path (rp_url V)))
                                           4))
                                 (a!276 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!279 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!303 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!304 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!305 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!306 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!307 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!308 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!314 (not ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))))
                                 (a!315 (SomeDOMElement (DOMElementResource
                                                          (rp_url V)
                                                          (@0SomeContentElement
                                                            (rp_content V)))))
                                 (a!316 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!317 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!318 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!319 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!320 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!321 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!330 (DOMElementResource
                                          (rp_url C1)
                                          (ContentElementFrame
                                            (Build_Frame (frame_src D1) E1)
                                            F1)))
                                 (a!336 (ite (= E1 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= E1 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!339 (ite (= Q 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= Q 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!342 (ite (= (frame_window D1) 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!345 (not (= (rp_hd_content_type
                                                  (rp_headers V))
                                                NoneContentType)))
                                 (a!347 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url I1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url I1)))))
                                 (a!348 (SomeOrigin (TupleOrigin (url_protocol (rp_url I1))
                                                                 (url_host (rp_url I1))
                                                                 (url_port (rp_url I1)))))
                                 (a!349 (OpaqueOrigin (@0url_path_data (url_path (rp_url I1)))))
                                 (a!351 (SomeOrigin (@0url_path_blob (url_path (rp_url I1)))))
                                 (a!355 (ite (= D 3)
                                             (@3ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 4)
                                                  (@4ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  (@defaultArrayprodOriginoptionCSP
                                                    (origin_csp X1)))))
                                 (a!360 (or (and (= U1 DOMTopLevel)
                                                 (= F2
                                                    (Build_ArrayoptionBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob)))
                                            (and (= U1 (DOMIndex V1)) (= F2 W1)))))
                           (let ((a!3 (and a!2
                                           (not ((_ is ResponseNoContent)
                                                  (rp_code R1)))))
                                 (a!9 (ite ((_ is ContentElementScript)
                                             (@0SomeContentElement
                                               (rp_content R1)))
                                           (= a!7 (rp_url R1))
                                           (= a!8 (rp_url R1))))
                                 (a!13 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeImage
                                            a!12))
                                 (a!19 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!18)))))
                                 (a!20 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!22 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!18)))))
                                 (a!23 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!25 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!18)))))
                                 (a!26 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!28 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!18)))))
                                 (a!29 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!31 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!18)))))
                                 (a!32 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!34 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!18)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!18)))))
                                 (a!35 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!18)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!18)))))
                                 (a!45 (ite ((_ is url_path_data)
                                              (url_path (wd_location S1)))
                                            (SomeOrigin a!44)
                                            NoneOrigin))
                                 (a!47 (ite ((_ is url_path_blob)
                                              (url_path (wd_location S1)))
                                            a!46
                                            NoneOrigin))
                                 (a!50 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!7)))))
                                 (a!51 (ite ((_ is url_path_blob)
                                              (url_path a!7))
                                            (SomeOrigin (@0url_path_blob (url_path a!7)))
                                            NoneOrigin))
                                 (a!55 (= (url_protocol a!7)
                                          (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!56 ((_ is SomePath)
                                         (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!57 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!59 ((_ is SomeInt)
                                         (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!60 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!61 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!62 ((_ is SomeProtocol)
                                         (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!63 (= (@0domain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!64 (= (@1subdomain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!66 ((_ is SomeoptionInt)
                                         (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!67 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!69 (not ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))))
                                 (a!71 (and ((_ is SomeDomain) (url_host a!7))
                                            ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))))
                                 (a!75 (not ((_ is CSPSrcNone)
                                              (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!84 (ite (= (@0DOMIndex Q1) 3)
                                            a!81
                                            (ite (= (@0DOMIndex Q1) 4)
                                                 a!82
                                                 a!83)))
                                 (a!98 (ite a!95
                                            (@2ArrayoptionBlob K1)
                                            (ite a!96
                                                 (@3ArrayoptionBlob K1)
                                                 (ite a!97
                                                      (@4ArrayoptionBlob K1)
                                                      (@defaultArrayoptionBlob
                                                        K1)))))
                                 (a!106 (ite (= a!105 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= a!105 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!109 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!108)))))
                                 (a!110 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!112 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!108)))))
                                 (a!113 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!115 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!108)))))
                                 (a!116 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!118 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!108)))))
                                 (a!119 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!121 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!108)))))
                                 (a!122 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!124 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!108)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!108)))))
                                 (a!125 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!108)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!108)))))
                                 (a!138 (ite (= (@0DOMIndex Q1) 3)
                                             a!135
                                             (ite (= (@0DOMIndex Q1) 4)
                                                  a!136
                                                  a!137)))
                                 (a!151 (ite (= (@0DOMIndex Q1) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!150
                                               a!145
                                               a!146
                                               a!147
                                               a!144
                                               a!149)
                                             (dm_body (dc_dom (wd_document S1)))))
                                 (a!158 (ite (= M1 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= M1 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!157)))
                                 (a!163 (and a!162
                                             (not ((_ is ResponseNoContent)
                                                    (rp_code V)))))
                                 (a!169 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!167 (rp_url V))
                                             (= a!168 (rp_url V))))
                                 (a!173 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeImage
                                             a!172))
                                 (a!183 (ite (= B1 2)
                                             a!179
                                             (ite (= B1 3)
                                                  a!180
                                                  (ite (= B1 4) a!181 a!182))))
                                 (a!190 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!189)))))
                                 (a!191 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!193 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!189)))))
                                 (a!194 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!196 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!189)))))
                                 (a!197 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!199 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!189)))))
                                 (a!200 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!202 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!189)))))
                                 (a!203 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!205 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!189)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!189)))))
                                 (a!206 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!189)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!189)))))
                                 (a!216 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             (SomeOrigin a!215)
                                             NoneOrigin))
                                 (a!218 (ite ((_ is url_path_blob)
                                               (url_path (wd_location W)))
                                             a!217
                                             NoneOrigin))
                                 (a!221 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!167)))))
                                 (a!222 (ite ((_ is url_path_blob)
                                               (url_path a!167))
                                             (SomeOrigin (@0url_path_blob (url_path a!167)))
                                             NoneOrigin))
                                 (a!226 (= (url_protocol a!167)
                                           (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!227 ((_ is SomePath)
                                          (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!228 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!230 ((_ is SomeInt)
                                          (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!231 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!232 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!233 ((_ is SomeProtocol)
                                          (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!234 (= (@0domain (@0SomeDomain (url_host a!167)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!235 (= (@1subdomain (@0SomeDomain (url_host a!167)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!237 ((_ is SomeoptionInt)
                                          (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!238 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!240 (not ((_ is domain)
                                               (@0SomeDomain (url_host a!167)))))
                                 (a!242 (and ((_ is SomeDomain)
                                               (url_host a!167))
                                             ((_ is domain)
                                               (@0SomeDomain (url_host a!167)))))
                                 (a!246 (not ((_ is CSPSrcNone)
                                               (@0SomeCSPSrc (csp_script_src a!211)))))
                                 (a!255 (ite (= (@0DOMIndex U) 3)
                                             a!252
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!253
                                                  a!254)))
                                 (a!269 (ite a!266
                                             (@2ArrayoptionBlob O)
                                             (ite a!267
                                                  (@3ArrayoptionBlob O)
                                                  (ite a!268
                                                       (@4ArrayoptionBlob O)
                                                       (@defaultArrayoptionBlob
                                                         O)))))
                                 (a!277 (ite (= a!276 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!276 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!280 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!279)))))
                                 (a!281 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!283 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!279)))))
                                 (a!284 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!286 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!279)))))
                                 (a!287 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!289 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!279)))))
                                 (a!290 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!292 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!279)))))
                                 (a!293 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!295 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!279)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!279)))))
                                 (a!296 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!279)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!279)))))
                                 (a!309 (ite (= (@0DOMIndex U) 3)
                                             a!306
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!307
                                                  a!308)))
                                 (a!322 (ite (= (@0DOMIndex U) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!321
                                               a!316
                                               a!317
                                               a!318
                                               a!315
                                               a!320)
                                             (dm_body (dc_dom (wd_document W)))))
                                 (a!331 (ite (= B1 4)
                                             (Build_ArrayoptionDOMElement
                                               a!177
                                               a!178
                                               a!179
                                               a!180
                                               (SomeDOMElement a!330)
                                               a!182)
                                             (dm_body (dc_dom (wd_document G1)))))
                                 (a!337 (ite (= E1 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= E1 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!336)))
                                 (a!340 (ite (= Q 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= Q 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!339)))
                                 (a!343 (ite (= (frame_window D1) 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!342)))
                                 (a!350 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             (SomeOrigin a!349)
                                             NoneOrigin))
                                 (a!352 (ite ((_ is url_path_blob)
                                               (url_path (rp_url I1)))
                                             a!351
                                             NoneOrigin))
                                 (a!356 (ite (= D 1)
                                             (@1ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 2)
                                                  (@2ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  a!355))))
                           (let ((a!10 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            (= a!6 (rp_url R1))
                                            a!9))
                                 (a!14 (ite ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeHTML
                                            a!13))
                                 (a!21 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!18)))
                                            (SomeDOMElement (DOMElementForm a!20))
                                            NoneDOMElement))
                                 (a!24 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!18)))
                                            (SomeDOMElement (DOMElementForm a!23))
                                            NoneDOMElement))
                                 (a!27 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!18)))
                                            (SomeDOMElement (DOMElementForm a!26))
                                            NoneDOMElement))
                                 (a!30 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!18)))
                                            (SomeDOMElement (DOMElementForm a!29))
                                            NoneDOMElement))
                                 (a!33 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!18)))
                                            (SomeDOMElement (DOMElementForm a!32))
                                            NoneDOMElement))
                                 (a!36 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!18)))
                                            (SomeDOMElement (DOMElementForm a!35))
                                            NoneDOMElement))
                                 (a!48 (ite ((_ is url_path_data)
                                              (url_path (wd_location S1)))
                                            NoneOrigin
                                            a!47))
                                 (a!52 (ite ((_ is ProtocolData)
                                              (url_protocol a!7))
                                            (ite ((_ is url_path_data)
                                                   (url_path a!7))
                                                 a!50
                                                 NoneOrigin)
                                            (ite ((_ is url_path_data)
                                                   (url_path a!7))
                                                 NoneOrigin
                                                 a!51)))
                                 (a!58 (and (not ((_ is url_path_blob)
                                                   (url_path a!7)))
                                            (not ((_ is url_path_data)
                                                   (url_path a!7)))
                                            (= (@0url_path_res (url_path a!7))
                                               a!57)))
                                 (a!65 (ite ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))
                                            a!63
                                            a!64))
                                 (a!68 (= (@0subdomain (@0SomeDomain (url_host a!7)))
                                          (@0SomeInt a!67)))
                                 (a!85 (ite (= (@0DOMIndex Q1) 1)
                                            a!79
                                            (ite (= (@0DOMIndex Q1) 2)
                                                 a!80
                                                 a!84)))
                                 (a!99 (@0SomeBlob (ite a!93
                                                        (@0ArrayoptionBlob K1)
                                                        (ite a!94
                                                             (@1ArrayoptionBlob
                                                               K1)
                                                             a!98))))
                                 (a!101 ((_ is SomeBlob)
                                          (ite a!93
                                               (@0ArrayoptionBlob K1)
                                               (ite a!94
                                                    (@1ArrayoptionBlob K1)
                                                    a!98))))
                                 (a!107 (ite (= a!105 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= a!105 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!106)))
                                 (a!111 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!110))
                                             NoneDOMElement))
                                 (a!114 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!113))
                                             NoneDOMElement))
                                 (a!117 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!116))
                                             NoneDOMElement))
                                 (a!120 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!119))
                                             NoneDOMElement))
                                 (a!123 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!122))
                                             NoneDOMElement))
                                 (a!126 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!108)))
                                             (SomeDOMElement (DOMElementForm a!125))
                                             NoneDOMElement))
                                 (a!139 (ite (= (@0DOMIndex Q1) 1)
                                             a!133
                                             (ite (= (@0DOMIndex Q1) 2)
                                                  a!134
                                                  a!138)))
                                 (a!152 (ite (= (@0DOMIndex Q1) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!150
                                               a!145
                                               a!144
                                               a!147
                                               a!148
                                               a!149)
                                             (ite (= (@0DOMIndex Q1) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!150
                                                    a!145
                                                    a!146
                                                    a!144
                                                    a!148
                                                    a!149)
                                                  a!151)))
                                 (a!159 (= (ite (= M1 0)
                                                (@0ArrayWindow (windows L1))
                                                a!158)
                                           O1))
                                 (a!170 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!166 (rp_url V))
                                             a!169))
                                 (a!174 (ite ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeHTML
                                             a!173))
                                 (a!184 (ite (= B1 0)
                                             a!177
                                             (ite (= B1 1) a!178 a!183)))
                                 (a!192 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!191))
                                             NoneDOMElement))
                                 (a!195 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!194))
                                             NoneDOMElement))
                                 (a!198 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!197))
                                             NoneDOMElement))
                                 (a!201 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!200))
                                             NoneDOMElement))
                                 (a!204 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!203))
                                             NoneDOMElement))
                                 (a!207 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!189)))
                                             (SomeDOMElement (DOMElementForm a!206))
                                             NoneDOMElement))
                                 (a!219 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             NoneOrigin
                                             a!218))
                                 (a!223 (ite ((_ is ProtocolData)
                                               (url_protocol a!167))
                                             (ite ((_ is url_path_data)
                                                    (url_path a!167))
                                                  a!221
                                                  NoneOrigin)
                                             (ite ((_ is url_path_data)
                                                    (url_path a!167))
                                                  NoneOrigin
                                                  a!222)))
                                 (a!229 (and (not ((_ is url_path_blob)
                                                    (url_path a!167)))
                                             (not ((_ is url_path_data)
                                                    (url_path a!167)))
                                             (= (@0url_path_res (url_path a!167))
                                                a!228)))
                                 (a!236 (ite ((_ is domain)
                                               (@0SomeDomain (url_host a!167)))
                                             a!234
                                             a!235))
                                 (a!239 (= (@0subdomain (@0SomeDomain (url_host a!167)))
                                           (@0SomeInt a!238)))
                                 (a!256 (ite (= (@0DOMIndex U) 1)
                                             a!250
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!251
                                                  a!255)))
                                 (a!270 (@0SomeBlob (ite a!264
                                                         (@0ArrayoptionBlob O)
                                                         (ite a!265
                                                              (@1ArrayoptionBlob
                                                                O)
                                                              a!269))))
                                 (a!272 ((_ is SomeBlob)
                                          (ite a!264
                                               (@0ArrayoptionBlob O)
                                               (ite a!265
                                                    (@1ArrayoptionBlob O)
                                                    a!269))))
                                 (a!278 (ite (= a!276 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!276 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!277)))
                                 (a!282 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!281))
                                             NoneDOMElement))
                                 (a!285 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!284))
                                             NoneDOMElement))
                                 (a!288 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!287))
                                             NoneDOMElement))
                                 (a!291 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!290))
                                             NoneDOMElement))
                                 (a!294 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!293))
                                             NoneDOMElement))
                                 (a!297 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!279)))
                                             (SomeDOMElement (DOMElementForm a!296))
                                             NoneDOMElement))
                                 (a!310 (ite (= (@0DOMIndex U) 1)
                                             a!304
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!305
                                                  a!309)))
                                 (a!323 (ite (= (@0DOMIndex U) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!321
                                               a!316
                                               a!315
                                               a!318
                                               a!319
                                               a!320)
                                             (ite (= (@0DOMIndex U) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!321
                                                    a!316
                                                    a!317
                                                    a!315
                                                    a!319
                                                    a!320)
                                                  a!322)))
                                 (a!332 (ite (= B1 2)
                                             (Build_ArrayoptionDOMElement
                                               a!177
                                               a!178
                                               (SomeDOMElement a!330)
                                               a!180
                                               a!181
                                               a!182)
                                             (ite (= B1 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!177
                                                    a!178
                                                    a!179
                                                    (SomeDOMElement a!330)
                                                    a!181
                                                    a!182)
                                                  a!331)))
                                 (a!338 (= (ite (= E1 0)
                                                (@0ArrayWindow (windows X))
                                                a!337)
                                           Y))
                                 (a!341 (= (ite (= Q 0)
                                                (@0ArrayWindow (windows P))
                                                a!340)
                                           S))
                                 (a!344 (= (ite (= (frame_window D1) 0)
                                                (@0ArrayWindow (windows X))
                                                a!343)
                                           I))
                                 (a!353 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             NoneOrigin
                                             a!352))
                                 (a!357 (= (ite (= D 0)
                                                (@0ArrayprodOriginoptionCSP
                                                  (origin_csp X1))
                                                a!356)
                                           (pairOriginoptionCSP E G))))
                           (let ((a!11 (or ((_ is ContentElementHTML)
                                             (@0SomeContentElement
                                               (rp_content R1)))
                                           a!10))
                                 (a!15 (= a!14
                                          (@0SomeContentType
                                            (rp_hd_content_type (rp_headers R1)))))
                                 (a!37 (Build_ArrayoptionDOMElement
                                         (ite ((_ is SomeHTMLElement)
                                                (@0ArrayoptionHTMLElement a!18))
                                              (ite a!19 NoneDOMElement a!21)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@1ArrayoptionHTMLElement a!18))
                                              (ite a!22 NoneDOMElement a!24)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@2ArrayoptionHTMLElement a!18))
                                              (ite a!25 NoneDOMElement a!27)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@3ArrayoptionHTMLElement a!18))
                                              (ite a!28 NoneDOMElement a!30)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@4ArrayoptionHTMLElement a!18))
                                              (ite a!31 NoneDOMElement a!33)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@defaultArrayoptionHTMLElement
                                                  a!18))
                                              (ite a!34 NoneDOMElement a!36)
                                              NoneDOMElement)))
                                 (a!49 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location S1)))
                                            a!45
                                            a!48))
                                 (a!53 (ite (or ((_ is ProtocolHTTPS)
                                                  (url_protocol a!7))
                                                ((_ is ProtocolHTTP)
                                                  (url_protocol a!7)))
                                            (SomeOrigin (TupleOrigin (url_protocol a!7)
                                                                     (url_host a!7)
                                                                     (url_port a!7)))
                                            a!52))
                                 (a!70 (ite ((_ is SomeInt) a!67)
                                            (and a!68
                                                 ((_ is SomeDomain)
                                                   (url_host a!7))
                                                 a!69)
                                            (and ((_ is SomeDomain)
                                                   (url_host a!7))
                                                 a!69)))
                                 (a!86 ((_ is SomeInt)
                                         (ite (= (@0DOMIndex Q1) 0) a!78 a!85)))
                                 (a!87 (@0SomeInt (ite (= (@0DOMIndex Q1) 0)
                                                       a!78
                                                       a!85)))
                                 (a!127 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!109 NoneDOMElement a!111)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!112 NoneDOMElement a!114)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!115 NoneDOMElement a!117)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!118 NoneDOMElement a!120)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!121 NoneDOMElement a!123)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!108))
                                               (ite a!124 NoneDOMElement a!126)
                                               NoneDOMElement)))
                                 (a!140 (@0SomeHTMLElement
                                          (ite (= (@0DOMIndex Q1) 0)
                                               a!132
                                               a!139)))
                                 (a!153 (ite (= (@0DOMIndex Q1) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!144
                                               a!145
                                               a!146
                                               a!147
                                               a!148
                                               a!149)
                                             (ite (= (@0DOMIndex Q1) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!150
                                                    a!144
                                                    a!146
                                                    a!147
                                                    a!148
                                                    a!149)
                                                  a!152)))
                                 (a!156 ((_ is SomeHTMLElement)
                                          (ite (= (@0DOMIndex Q1) 0)
                                               a!132
                                               a!139)))
                                 (a!171 (or ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            a!170))
                                 (a!175 (= a!174
                                           (@0SomeContentType
                                             (rp_hd_content_type (rp_headers V)))))
                                 (a!185 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!184)))
                                           D1))
                                 (a!186 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!184)))
                                           F1))
                                 (a!187 (not ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!184)))))
                                 (a!208 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!190 NoneDOMElement a!192)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!193 NoneDOMElement a!195)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!196 NoneDOMElement a!198)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!199 NoneDOMElement a!201)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!202 NoneDOMElement a!204)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!189))
                                               (ite a!205 NoneDOMElement a!207)
                                               NoneDOMElement)))
                                 (a!220 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location W)))
                                             a!216
                                             a!219))
                                 (a!224 (ite (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!167))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!167)))
                                             (SomeOrigin (TupleOrigin (url_protocol a!167)
                                                                      (url_host a!167)
                                                                      (url_port a!167)))
                                             a!223))
                                 (a!241 (ite ((_ is SomeInt) a!238)
                                             (and a!239
                                                  ((_ is SomeDomain)
                                                    (url_host a!167))
                                                  a!240)
                                             (and ((_ is SomeDomain)
                                                    (url_host a!167))
                                                  a!240)))
                                 (a!257 ((_ is SomeInt)
                                          (ite (= (@0DOMIndex U) 0) a!249 a!256)))
                                 (a!258 (@0SomeInt (ite (= (@0DOMIndex U) 0)
                                                        a!249
                                                        a!256)))
                                 (a!298 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!280 NoneDOMElement a!282)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!283 NoneDOMElement a!285)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!286 NoneDOMElement a!288)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!289 NoneDOMElement a!291)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!292 NoneDOMElement a!294)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!279))
                                               (ite a!295 NoneDOMElement a!297)
                                               NoneDOMElement)))
                                 (a!311 (@0SomeHTMLElement
                                          (ite (= (@0DOMIndex U) 0) a!303 a!310)))
                                 (a!324 (ite (= (@0DOMIndex U) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!315
                                               a!316
                                               a!317
                                               a!318
                                               a!319
                                               a!320)
                                             (ite (= (@0DOMIndex U) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!321
                                                    a!315
                                                    a!317
                                                    a!318
                                                    a!319
                                                    a!320)
                                                  a!323)))
                                 (a!327 ((_ is SomeHTMLElement)
                                          (ite (= (@0DOMIndex U) 0) a!303 a!310)))
                                 (a!328 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!184)))))
                                 (a!329 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!184)))))
                                 (a!333 (ite (= B1 0)
                                             (Build_ArrayoptionDOMElement
                                               (SomeDOMElement a!330)
                                               a!178
                                               a!179
                                               a!180
                                               a!181
                                               a!182)
                                             (ite (= B1 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!177
                                                    (SomeDOMElement a!330)
                                                    a!179
                                                    a!180
                                                    a!181
                                                    a!182)
                                                  a!332)))
                                 (a!354 (ite ((_ is ProtocolData)
                                               (url_protocol (rp_url I1)))
                                             a!350
                                             a!353)))
                           (let ((a!16 (or (not ((_ is SomeContentElement)
                                                  (rp_content R1)))
                                           a!5
                                           (and a!11 a!15)))
                                 (a!38 (Build_Document (+ 1 P1)
                                                       (ft_correlator N1)
                                                       (rp_headers R1)
                                                       (@0ContentElementHTML
                                                         (@0SomeContentElement
                                                           (rp_content R1)))
                                                       (Build_DOM (ft_correlator N1)
                                                                  0
                                                                  a!37)
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!54 (= (SomeOrigin (@0SomeOrigin (ite a!42
                                                                         a!43
                                                                         a!49)))
                                          a!53))
                                 (a!72 (and (or (not a!56) a!58)
                                            (or (not a!59)
                                                (= (url_port a!7)
                                                   (SomeInt a!60)))
                                            (or (= (url_protocol a!7) a!61)
                                                (not a!62))
                                            a!65
                                            (ite a!66 a!70 a!71)
                                            ((_ is SomeDomain) (url_host a!7))))
                                 (a!88 (ite (= a!87 3)
                                            (@3ArrayWindow (windows L1))
                                            (ite (= a!87 4)
                                                 (@4ArrayWindow (windows L1))
                                                 (@defaultArrayWindow
                                                   (windows L1)))))
                                 (a!128 (Build_Document (+ 1 P1)
                                                        (ft_correlator N1)
                                                        (rp_headers R1)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content R1)))
                                                        (Build_DOM (ft_correlator N1)
                                                                   0
                                                                   a!127)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!141 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (= a!140 (HTMLScript a!7))
                                             (= a!140 (HTMLFrame a!8))))
                                 (a!154 (Build_DOM (dm_nonce (dc_dom (wd_document S1)))
                                                   (dm_head (dc_dom (wd_document S1)))
                                                   a!153))
                                 (a!176 (or (not ((_ is SomeContentElement)
                                                   (rp_content V)))
                                            a!165
                                            (and a!171 a!175)))
                                 (a!209 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@0ContentElementHTML
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!208)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!225 (= (SomeOrigin (@0SomeOrigin (ite a!213
                                                                          a!214
                                                                          a!220)))
                                           a!224))
                                 (a!243 (and (or (not a!227) a!229)
                                             (or (not a!230)
                                                 (= (url_port a!167)
                                                    (SomeInt a!231)))
                                             (or (= (url_protocol a!167) a!232)
                                                 (not a!233))
                                             a!236
                                             (ite a!237 a!241 a!242)
                                             ((_ is SomeDomain)
                                               (url_host a!167))))
                                 (a!259 (ite (= a!258 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!258 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!299 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!298)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!312 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!311 (HTMLScript a!167))
                                             (= a!311 (HTMLFrame a!168))))
                                 (a!325 (Build_DOM (dm_nonce (dc_dom (wd_document W)))
                                                   (dm_head (dc_dom (wd_document W)))
                                                   a!324))
                                 (a!334 (Build_DOM (dm_nonce (dc_dom (wd_document G1)))
                                                   (dm_head (dc_dom (wd_document G1)))
                                                   a!333))
                                 (a!358 (and (c_origin_wide_csp (config X1))
                                             (= (ite a!347 a!348 a!354)
                                                (SomeOrigin F))
                                             a!357
                                             (= E F)
                                             (= (rp_hd_csp (rp_headers I1)) G))))
                           (let ((a!39 (and a!17
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            (= O1
                                               (Build_Window (ft_correlator N1)
                                                             NoneInt
                                                             (rp_url R1)
                                                             NoneDomain
                                                             a!38))))
                                 (a!73 (ite ((_ is CSPSrcScheme)
                                              (@0SomeCSPSrc (csp_script_src a!40)))
                                            a!55
                                            a!72))
                                 (a!89 (ite (= a!87 1)
                                            (@1ArrayWindow (windows L1))
                                            (ite (= a!87 2)
                                                 (@2ArrayWindow (windows L1))
                                                 a!88)))
                                 (a!129 (= (ite (= a!105 0)
                                                (@0ArrayWindow (windows L1))
                                                a!107)
                                           (Build_Window (ft_correlator N1)
                                                         (SomeInt M1)
                                                         (rp_url R1)
                                                         NoneDomain
                                                         a!128)))
                                 (a!142 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (= a!140 (HTMLImage a!6))
                                             a!141))
                                 (a!155 (Build_Window (wd_nonce S1)
                                                      (wd_parent S1)
                                                      (wd_location S1)
                                                      (wd_document_domain S1)
                                                      (Build_Document (+ 1 P1)
                                                                      (dc_nonce (wd_document S1))
                                                                      (dc_headers (wd_document S1))
                                                                      (dc_html (wd_document S1))
                                                                      a!154
                                                                      (dc_init (wd_document S1)))))
                                 (a!210 (and a!188
                                             ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= S
                                                (Build_Window (ft_correlator R)
                                                              NoneInt
                                                              (rp_url V)
                                                              NoneDomain
                                                              a!209))))
                                 (a!244 (ite ((_ is CSPSrcScheme)
                                               (@0SomeCSPSrc (csp_script_src a!211)))
                                             a!226
                                             a!243))
                                 (a!260 (ite (= a!258 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!258 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!259)))
                                 (a!300 (= (ite (= a!276 0)
                                                (@0ArrayWindow (windows P))
                                                a!278)
                                           (Build_Window (ft_correlator R)
                                                         (SomeInt Q)
                                                         (rp_url V)
                                                         NoneDomain
                                                         a!299)))
                                 (a!313 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!311 (HTMLImage a!166))
                                             a!312))
                                 (a!326 (Build_Window (wd_nonce W)
                                                      (wd_parent W)
                                                      (wd_location W)
                                                      (wd_document_domain W)
                                                      (Build_Document (+ 1 T)
                                                                      (dc_nonce (wd_document W))
                                                                      (dc_headers (wd_document W))
                                                                      (dc_html (wd_document W))
                                                                      a!325
                                                                      (dc_init (wd_document W)))))
                                 (a!335 (Build_Window (wd_nonce G1)
                                                      (wd_parent G1)
                                                      (wd_location G1)
                                                      (wd_document_domain G1)
                                                      (Build_Document (+ 1 A1)
                                                                      (dc_nonce (wd_document G1))
                                                                      (dc_headers (wd_document G1))
                                                                      (dc_html (wd_document G1))
                                                                      a!334
                                                                      (dc_init (wd_document G1)))))
                                 (a!359 (or (not (c_origin_wide_csp (config X1)))
                                            a!358)))
                           (let ((a!74 (ite ((_ is CSPSrcSelf)
                                              (@0SomeCSPSrc (csp_script_src a!40)))
                                            a!54
                                            a!73))
                                 (a!90 (wd_document (ite (= a!87 0)
                                                         (@0ArrayWindow (windows L1))
                                                         a!89)))
                                 (a!245 (ite ((_ is CSPSrcSelf)
                                               (@0SomeCSPSrc (csp_script_src a!211)))
                                             a!225
                                             a!244))
                                 (a!261 (wd_document (ite (= a!258 0)
                                                          (@0ArrayWindow (windows P))
                                                          a!260))))
                           (let ((a!76 (or (not ((_ is SomeCSPSrc)
                                                  (csp_script_src a!40)))
                                           (not a!41)
                                           (and a!74
                                                ((_ is SomeOrigin)
                                                  (ite a!42 a!43 a!49))
                                                a!75)))
                                 (a!92 (ite (c_csp_inherit_local_from_initiator
                                              (config L1))
                                            (= (rp_hd_csp (rp_headers R1))
                                               (rp_hd_csp (dc_headers a!90)))
                                            a!91))
                                 (a!247 (or (not ((_ is SomeCSPSrc)
                                                   (csp_script_src a!211)))
                                            (not a!212)
                                            (and a!245
                                                 ((_ is SomeOrigin)
                                                   (ite a!213 a!214 a!220))
                                                 a!246)))
                                 (a!263 (ite (c_csp_inherit_local_from_initiator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (rp_hd_csp (dc_headers a!261)))
                                             a!262)))
                           (let ((a!100 (ite (c_csp_inherit_blob_from_creator
                                               (config L1))
                                             (= (rp_hd_csp (rp_headers R1))
                                                (blob_csp a!99))
                                             (ite a!86 a!92 a!91)))
                                 (a!271 (ite (c_csp_inherit_blob_from_creator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (blob_csp a!270))
                                             (ite a!257 a!263 a!262))))
                           (let ((a!102 (ite ((_ is url_path_blob)
                                               (url_path (rp_url R1)))
                                             (and a!100 a!101)
                                             (ite a!86 a!92 a!91)))
                                 (a!273 (ite ((_ is url_path_blob)
                                               (url_path (rp_url V)))
                                             (and a!271 a!272)
                                             (ite a!257 a!263 a!262))))
                           (let ((a!103 (ite ((_ is url_path_data)
                                               (url_path (rp_url R1)))
                                             (ite a!86 a!92 a!91)
                                             a!102))
                                 (a!274 (ite ((_ is url_path_data)
                                               (url_path (rp_url V)))
                                             (ite a!257 a!263 a!262)
                                             a!273)))
                           (let ((a!104 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url R1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url R1)))
                                            a!103))
                                 (a!275 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url V)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url V)))
                                            a!274)))
                           (let ((a!130 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (and a!76 (= a!77 P1))
                                             (and a!104 a!129)))
                                 (a!301 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (and a!247 (= a!248 T))
                                             (and a!275 a!300))))
                           (let ((a!131 (or ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            a!130))
                                 (a!302 (or ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            a!301)))
                           (let ((a!161 (and (or ((_ is ResponseOk)
                                                   (rp_code R1))
                                                 a!3)
                                             (or ((_ is EmitterClient)
                                                   (ft_emitter N1))
                                                 a!4)
                                             a!16
                                             (= A2 P1)
                                             (ite ((_ is DOMTopLevel) Q1)
                                                  a!39
                                                  (and a!131
                                                       a!142
                                                       a!143
                                                       (= O1 a!155)
                                                       a!156))
                                             (= D2 O1)
                                             (= H1 S1)
                                             a!159
                                             (= Y1 J1)
                                             (= J1 (DOMPath nilInt Q1))
                                             (= X1 L1)
                                             (= (ft_response N1)
                                                (SomeResponse R1))
                                             (= (rp_code R1) ResponseOk)
                                             (= B2 N1)
                                             (= I1 R1)
                                             ((_ is SomeContentElement)
                                               (rp_content R1))
                                             a!160
                                             (= W1 K1)))
                                 (a!346 (and (or ((_ is ResponseOk) (rp_code V))
                                                 a!163)
                                             (or ((_ is EmitterClient)
                                                   (ft_emitter R))
                                                 a!164)
                                             a!176
                                             (= A2 A1)
                                             (= A1 T)
                                             a!185
                                             a!186
                                             a!187
                                             (ite ((_ is DOMTopLevel) U)
                                                  a!210
                                                  (and a!302
                                                       a!313
                                                       a!314
                                                       (= S a!326)
                                                       a!327))
                                             a!328
                                             a!329
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!184)))
                                             ((_ is SomeDOMElement) a!184)
                                             (= D2 Z)
                                             (= H1 G1)
                                             (= Z a!335)
                                             (= Y S)
                                             (= I W)
                                             a!338
                                             a!341
                                             a!344
                                             (= Y1 H)
                                             (= N (DOMPath J K))
                                             (= N (DOMPath nilInt U))
                                             (= H (DOMPath (consInt B1 J) K))
                                             (= X1 X)
                                             (= X P)
                                             (= (ft_response R)
                                                (SomeResponse V))
                                             (= (rp_code V) ResponseOk)
                                             (= B2 M)
                                             (= M R)
                                             (= I1 C1)
                                             (= C1 V)
                                             ((_ is SomeContentElement)
                                               (rp_content V))
                                             a!345
                                             (= W1 L)
                                             (= L O))))
                           (let ((a!361 (and (Reachable X1 Z1 A)
                                             (= A
                                                (Build_State A2
                                                             B2
                                                             C2
                                                             H1
                                                             E2
                                                             W1
                                                             G2))
                                             (= B a!1)
                                             (= Y1 (DOMPath T1 U1))
                                             (or a!161 a!346)
                                             a!359
                                             a!360
                                             (= C
                                                (consEvent (EvDOMUpdate Y1) Z1)))))
                             (=> a!361 (Reachable X1 C B))))))))))))))))))
                           :weight 0))))
      (a!88 (asserted (forall ((A Script)
                               (B NestedDOMPath)
                               (C NestedDOMPath)
                               (D Int)
                               (E Window)
                               (F HTML)
                               (G Frame)
                               (H listInt)
                               (I DOMSelector)
                               (J Window)
                               (K Window)
                               (L Global)
                               (M Global)
                               (N NestedDOMPath)
                               (O DOMSelector)
                               (P Window)
                               (Q Window)
                               (R Window)
                               (S Global)
                               (T Global)
                               (U NestedDOMPath)
                               (V DOMSelector)
                               (W Window)
                               (X Window)
                               (Y NestedDOMPath)
                               (Z listInt)
                               (A1 Int)
                               (B1 Window)
                               (C1 Script)
                               (D1 Form)
                               (E1 NestedDOMPath)
                               (F1 NestedDOMPath)
                               (G1 Int)
                               (H1 Window)
                               (I1 HTML)
                               (J1 Frame)
                               (K1 listInt)
                               (L1 DOMSelector)
                               (M1 Window)
                               (N1 Window)
                               (O1 Global)
                               (P1 Global)
                               (Q1 NestedDOMPath)
                               (R1 DOMSelector)
                               (S1 Window)
                               (T1 Window)
                               (U1 Window)
                               (V1 Global)
                               (W1 Global)
                               (X1 NestedDOMPath)
                               (Y1 DOMSelector)
                               (Z1 Window)
                               (A2 Window)
                               (B2 NestedDOMPath)
                               (C2 listInt)
                               (D2 Int)
                               (E2 Window)
                               (F2 Form)
                               (G2 Request)
                               (H2 Int)
                               (I2 Script)
                               (J2 NestedDOMPath)
                               (K2 NestedDOMPath)
                               (L2 Int)
                               (M2 Window)
                               (N2 HTML)
                               (O2 Frame)
                               (P2 listInt)
                               (Q2 DOMSelector)
                               (R2 Window)
                               (S2 Window)
                               (T2 Global)
                               (U2 Global)
                               (V2 NestedDOMPath)
                               (W2 DOMSelector)
                               (X2 Window)
                               (Y2 Window)
                               (Z2 Window)
                               (A3 Global)
                               (B3 Global)
                               (C3 NestedDOMPath)
                               (D3 DOMSelector)
                               (E3 Window)
                               (F3 Window)
                               (G3 NestedDOMPath)
                               (H3 listInt)
                               (I3 Int)
                               (J3 Window)
                               (K3 Script)
                               (L3 Global)
                               (M3 Window)
                               (N3 Window)
                               (O3 State)
                               (P3 State)
                               (Q3 listEvent)
                               (R3 Int)
                               (S3 Int)
                               (T3 Int)
                               (U3 Origin)
                               (V3 Blob)
                               (W3 Int)
                               (X3 Int)
                               (Y3 Int)
                               (Z3 Origin)
                               (A4 Blob)
                               (B4 Int)
                               (C4 Int)
                               (D4 FetchEngine)
                               (E4 Int)
                               (F4 SetCookie)
                               (G4 ArrayoptionSetCookie)
                               (H4 ArrayoptionSetCookie)
                               (I4 listEvent)
                               (J4 Int)
                               (K4 ServiceWorker)
                               (L4 ArrayoptionSetCookie)
                               (M4 ArrayoptionBlob)
                               (N4 ArrayoptionStorageItem))
                        (! (let ((a!1 (ite (= C4 3)
                                           (@3ArrayResponse (responses L3))
                                           (ite (= C4 4)
                                                (@4ArrayResponse (responses L3))
                                                (@defaultArrayResponse
                                                  (responses L3)))))
                                 (a!5 (SomeprodprodEmitterIntInt
                                        (pairprodEmitterIntInt
                                          (pairEmitterInt (ft_emitter D4) B4)
                                          C4)))
                                 (a!13 (ite (= B4 3)
                                            (@3ArrayRequest (requests L3))
                                            (ite (= B4 4)
                                                 (@4ArrayRequest (requests L3))
                                                 (@defaultArrayRequest
                                                   (requests L3)))))
                                 (a!16 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!17 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!18 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!19 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!20 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!21 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!29 (ite (= (frame_window J1) 3)
                                            (@3ArrayWindow (windows O1))
                                            (ite (= (frame_window J1) 4)
                                                 (@4ArrayWindow (windows O1))
                                                 (@defaultArrayWindow
                                                   (windows O1)))))
                                 (a!34 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!35 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!36 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!37 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!38 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!39 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!43 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!44 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!45 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!46 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!47 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!48 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!56 (ite (= (frame_window G) 3)
                                            (@3ArrayWindow (windows L))
                                            (ite (= (frame_window G) 4)
                                                 (@4ArrayWindow (windows L))
                                                 (@defaultArrayWindow
                                                   (windows L)))))
                                 (a!61 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!62 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!63 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!64 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!65 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!66 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!73 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!74 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!75 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!76 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!77 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!78 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!86 (ite (= (frame_window O2) 3)
                                            (@3ArrayWindow (windows T2))
                                            (ite (= (frame_window O2) 4)
                                                 (@4ArrayWindow (windows T2))
                                                 (@defaultArrayWindow
                                                   (windows T2)))))
                                 (a!91 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!92 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!93 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!94 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!95 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!96 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!102 (ite (= H2 3)
                                             (@3ArrayEmitter (emitters L3))
                                             (ite (= H2 4)
                                                  (@4ArrayEmitter (emitters L3))
                                                  (@defaultArrayEmitter
                                                    (emitters L3)))))
                                 (a!108 (ite (= B4 3)
                                             (@3ArrayInt (server_responses L3))
                                             (ite (= B4 4)
                                                  (@4ArrayInt (server_responses L3))
                                                  (@defaultArrayInt (server_responses L3)))))
                                 (a!121 (ite (= W3 3)
                                             (@3ArrayContentElement
                                               (data_urls L3))
                                             (ite (= W3 4)
                                                  (@4ArrayContentElement
                                                    (data_urls L3))
                                                  (@defaultArrayContentElement
                                                    (data_urls L3)))))
                                 (a!124 (ite (= Y3 2)
                                             (@2ArrayoptionBlob M4)
                                             (ite (= Y3 3)
                                                  (@3ArrayoptionBlob M4)
                                                  (ite (= Y3 4)
                                                       (@4ArrayoptionBlob M4)
                                                       (@defaultArrayoptionBlob
                                                         M4)))))
                                 (a!130 (ite (= R3 3)
                                             (@3ArrayContentElement
                                               (data_urls L3))
                                             (ite (= R3 4)
                                                  (@4ArrayContentElement
                                                    (data_urls L3))
                                                  (@defaultArrayContentElement
                                                    (data_urls L3)))))
                                 (a!133 (ite (= T3 2)
                                             (@2ArrayoptionBlob M4)
                                             (ite (= T3 3)
                                                  (@3ArrayoptionBlob M4)
                                                  (ite (= T3 4)
                                                       (@4ArrayoptionBlob M4)
                                                       (@defaultArrayoptionBlob
                                                         M4)))))
                                 (a!138 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location N3)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location N3)))))
                                 (a!139 (SomeOrigin (TupleOrigin (url_protocol (wd_location N3))
                                                                 (url_host (wd_location N3))
                                                                 (url_port (wd_location N3)))))
                                 (a!140 (OpaqueOrigin (@0url_path_data (url_path (wd_location N3)))))
                                 (a!142 (SomeOrigin (@0url_path_blob (url_path (wd_location N3)))))
                                 (a!162 (ite (= E4 2)
                                             (@2ArrayoptionSetCookie G4)
                                             (ite (= E4 3)
                                                  (@3ArrayoptionSetCookie G4)
                                                  (ite (= E4 4)
                                                       (@4ArrayoptionSetCookie
                                                         G4)
                                                       (@defaultArrayoptionSetCookie
                                                         G4)))))
                                 (a!164 (ite (= E4 3)
                                             (Build_ArrayoptionSetCookie
                                               (@0ArrayoptionSetCookie G4)
                                               (@1ArrayoptionSetCookie G4)
                                               (@2ArrayoptionSetCookie G4)
                                               (SomeSetCookie F4)
                                               (@4ArrayoptionSetCookie G4)
                                               (@defaultArrayoptionSetCookie G4))
                                             (ite (= E4 4)
                                                  (Build_ArrayoptionSetCookie
                                                    (@0ArrayoptionSetCookie G4)
                                                    (@1ArrayoptionSetCookie G4)
                                                    (@2ArrayoptionSetCookie G4)
                                                    (@3ArrayoptionSetCookie G4)
                                                    (SomeSetCookie F4)
                                                    (@defaultArrayoptionSetCookie
                                                      G4))
                                                  G4)))
                                 (a!167 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!168 (= (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!169 (= (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4)))
                                 (a!171 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!172 (= (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!173 (= (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4)))
                                 (a!175 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!176 (= (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!177 (= (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4)))
                                 (a!179 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!180 (= (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!181 (= (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4)))
                                 (a!183 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!184 (= (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!185 (= (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4)))
                                 (a!187 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             H4)))
                                           (sc_reg_domain F4)))
                                 (a!188 (= (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       H4)))
                                           (sc_path F4)))
                                 (a!189 (= (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       H4)))
                                           (sc_name F4))))
                           (let ((a!2 (ite (= C4 1)
                                           (@1ArrayResponse (responses L3))
                                           (ite (= C4 2)
                                                (@2ArrayResponse (responses L3))
                                                a!1)))
                                 (a!6 (ite (= (ft_correlator D4) 4)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             a!5
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history D4)))
                                           (ft_history D4)))
                                 (a!14 (ite (= B4 1)
                                            (@1ArrayRequest (requests L3))
                                            (ite (= B4 2)
                                                 (@2ArrayRequest (requests L3))
                                                 a!13)))
                                 (a!22 (ite (= G1 2)
                                            a!18
                                            (ite (= G1 3)
                                                 a!19
                                                 (ite (= G1 4) a!20 a!21))))
                                 (a!30 (ite (= (frame_window J1) 1)
                                            (@1ArrayWindow (windows O1))
                                            (ite (= (frame_window J1) 2)
                                                 (@2ArrayWindow (windows O1))
                                                 a!29)))
                                 (a!40 (ite (= D2 2)
                                            a!36
                                            (ite (= D2 3)
                                                 a!37
                                                 (ite (= D2 4) a!38 a!39))))
                                 (a!49 (ite (= D 2)
                                            a!45
                                            (ite (= D 3)
                                                 a!46
                                                 (ite (= D 4) a!47 a!48))))
                                 (a!57 (ite (= (frame_window G) 1)
                                            (@1ArrayWindow (windows L))
                                            (ite (= (frame_window G) 2)
                                                 (@2ArrayWindow (windows L))
                                                 a!56)))
                                 (a!67 (ite (= A1 2)
                                            a!63
                                            (ite (= A1 3)
                                                 a!64
                                                 (ite (= A1 4) a!65 a!66))))
                                 (a!79 (ite (= L2 2)
                                            a!75
                                            (ite (= L2 3)
                                                 a!76
                                                 (ite (= L2 4) a!77 a!78))))
                                 (a!87 (ite (= (frame_window O2) 1)
                                            (@1ArrayWindow (windows T2))
                                            (ite (= (frame_window O2) 2)
                                                 (@2ArrayWindow (windows T2))
                                                 a!86)))
                                 (a!97 (ite (= I3 2)
                                            a!93
                                            (ite (= I3 3)
                                                 a!94
                                                 (ite (= I3 4) a!95 a!96))))
                                 (a!103 (ite (= H2 1)
                                             (@1ArrayEmitter (emitters L3))
                                             (ite (= H2 2)
                                                  (@2ArrayEmitter (emitters L3))
                                                  a!102)))
                                 (a!109 (ite (= B4 1)
                                             (@1ArrayInt (server_responses L3))
                                             (ite (= B4 2)
                                                  (@2ArrayInt (server_responses L3))
                                                  a!108)))
                                 (a!122 (ite (= W3 1)
                                             (@1ArrayContentElement
                                               (data_urls L3))
                                             (ite (= W3 2)
                                                  (@2ArrayContentElement
                                                    (data_urls L3))
                                                  a!121)))
                                 (a!125 (= (ite (= Y3 0)
                                                (@0ArrayoptionBlob M4)
                                                (ite (= Y3 1)
                                                     (@1ArrayoptionBlob M4)
                                                     a!124))
                                           (SomeBlob A4)))
                                 (a!131 (ite (= R3 1)
                                             (@1ArrayContentElement
                                               (data_urls L3))
                                             (ite (= R3 2)
                                                  (@2ArrayContentElement
                                                    (data_urls L3))
                                                  a!130)))
                                 (a!134 (= (ite (= T3 0)
                                                (@0ArrayoptionBlob M4)
                                                (ite (= T3 1)
                                                     (@1ArrayoptionBlob M4)
                                                     a!133))
                                           (SomeBlob V3)))
                                 (a!141 (ite ((_ is url_path_data)
                                               (url_path (wd_location N3)))
                                             (SomeOrigin a!140)
                                             NoneOrigin))
                                 (a!143 (ite ((_ is url_path_blob)
                                               (url_path (wd_location N3)))
                                             a!142
                                             NoneOrigin))
                                 (a!163 (= (ite (= E4 0)
                                                (@0ArrayoptionSetCookie G4)
                                                (ite (= E4 1)
                                                     (@1ArrayoptionSetCookie G4)
                                                     a!162))
                                           NoneSetCookie))
                                 (a!165 (ite (= E4 1)
                                             (Build_ArrayoptionSetCookie
                                               (@0ArrayoptionSetCookie G4)
                                               (SomeSetCookie F4)
                                               (@2ArrayoptionSetCookie G4)
                                               (@3ArrayoptionSetCookie G4)
                                               (@4ArrayoptionSetCookie G4)
                                               (@defaultArrayoptionSetCookie G4))
                                             (ite (= E4 2)
                                                  (Build_ArrayoptionSetCookie
                                                    (@0ArrayoptionSetCookie G4)
                                                    (@1ArrayoptionSetCookie G4)
                                                    (SomeSetCookie F4)
                                                    (@3ArrayoptionSetCookie G4)
                                                    (@4ArrayoptionSetCookie G4)
                                                    (@defaultArrayoptionSetCookie
                                                      G4))
                                                  a!164)))
                                 (a!170 (ite (and a!167 a!168 a!169)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!174 (ite (and a!171 a!172 a!173)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!178 (ite (and a!175 a!176 a!177)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!182 (ite (and a!179 a!180 a!181)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!186 (ite (and a!183 a!184 a!185)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!190 (ite (and a!187 a!188 a!189)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                               H4))))))
                           (let ((a!3 (EvResponse (ite (= C4 0)
                                                       (@0ArrayResponse (responses L3))
                                                       a!2)
                                                  (ft_correlator D4)))
                                 (a!4 (SomeResponse (ite (= C4 0)
                                                         (@0ArrayResponse (responses L3))
                                                         a!2)))
                                 (a!7 (ite (= (ft_correlator D4) 3)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             a!5
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history D4)))
                                           a!6))
                                 (a!12 (rp_url (ite (= C4 0)
                                                    (@0ArrayResponse (responses L3))
                                                    a!2)))
                                 (a!15 (= (ft_request D4)
                                          (ite (= B4 0)
                                               (@0ArrayRequest (requests L3))
                                               a!14)))
                                 (a!23 (ite (= G1 0)
                                            a!16
                                            (ite (= G1 1) a!17 a!22)))
                                 (a!31 (= (ite (= (frame_window J1) 0)
                                               (@0ArrayWindow (windows O1))
                                               a!30)
                                          M1))
                                 (a!41 (ite (= D2 0)
                                            a!34
                                            (ite (= D2 1) a!35 a!40)))
                                 (a!50 (ite (= D 0)
                                            a!43
                                            (ite (= D 1) a!44 a!49)))
                                 (a!58 (= (ite (= (frame_window G) 0)
                                               (@0ArrayWindow (windows L))
                                               a!57)
                                          J))
                                 (a!68 (ite (= A1 0)
                                            a!61
                                            (ite (= A1 1) a!62 a!67)))
                                 (a!80 (ite (= L2 0)
                                            a!73
                                            (ite (= L2 1) a!74 a!79)))
                                 (a!88 (= (ite (= (frame_window O2) 0)
                                               (@0ArrayWindow (windows T2))
                                               a!87)
                                          R2))
                                 (a!98 (ite (= I3 0)
                                            a!91
                                            (ite (= I3 1) a!92 a!97)))
                                 (a!104 (= (ite (= H2 0)
                                                (@0ArrayEmitter (emitters L3))
                                                a!103)
                                           (EmitterScript J2 I2)))
                                 (a!107 (rq_url (ite (= B4 0)
                                                     (@0ArrayRequest (requests L3))
                                                     a!14)))
                                 (a!110 (= (ite (= B4 0)
                                                (@0ArrayInt (server_responses L3))
                                                a!109)
                                           0))
                                 (a!111 (= (ite (= B4 0)
                                                (@0ArrayInt (server_responses L3))
                                                a!109)
                                           1))
                                 (a!112 (= (ite (= B4 0)
                                                (@0ArrayInt (server_responses L3))
                                                a!109)
                                           2))
                                 (a!113 (= (ite (= B4 0)
                                                (@0ArrayInt (server_responses L3))
                                                a!109)
                                           3))
                                 (a!114 (= (ite (= B4 0)
                                                (@0ArrayInt (server_responses L3))
                                                a!109)
                                           4))
                                 (a!120 (rp_content (ite (= C4 0)
                                                         (@0ArrayResponse (responses L3))
                                                         a!2)))
                                 (a!123 (SomeContentElement
                                          (ite (= W3 0)
                                               (@0ArrayContentElement
                                                 (data_urls L3))
                                               a!122)))
                                 (a!128 (rp_headers (ite (= C4 0)
                                                         (@0ArrayResponse (responses L3))
                                                         a!2)))
                                 (a!129 (rp_code (ite (= C4 0)
                                                      (@0ArrayResponse (responses L3))
                                                      a!2)))
                                 (a!132 (SomeContentElement
                                          (ite (= R3 0)
                                               (@0ArrayContentElement
                                                 (data_urls L3))
                                               a!131)))
                                 (a!144 (ite ((_ is url_path_data)
                                               (url_path (wd_location N3)))
                                             NoneOrigin
                                             a!143))
                                 (a!166 (= L4
                                           (ite (= E4 0)
                                                (Build_ArrayoptionSetCookie
                                                  (SomeSetCookie F4)
                                                  (@1ArrayoptionSetCookie G4)
                                                  (@2ArrayoptionSetCookie G4)
                                                  (@3ArrayoptionSetCookie G4)
                                                  (@4ArrayoptionSetCookie G4)
                                                  (@defaultArrayoptionSetCookie
                                                    G4))
                                                a!165)))
                                 (a!191 (Build_ArrayoptionSetCookie
                                          (ite ((_ is SomeSetCookie)
                                                 (@0ArrayoptionSetCookie H4))
                                               a!170
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@1ArrayoptionSetCookie H4))
                                               a!174
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@2ArrayoptionSetCookie H4))
                                               a!178
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@3ArrayoptionSetCookie H4))
                                               a!182
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@4ArrayoptionSetCookie H4))
                                               a!186
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@defaultArrayoptionSetCookie
                                                   H4))
                                               a!190
                                               NoneSetCookie))))
                           (let ((a!8 (ite (= (ft_correlator D4) 2)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             a!5
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history D4)))
                                           a!7))
                                 (a!24 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!23)))
                                          J1))
                                 (a!25 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!23)))
                                          I1))
                                 (a!26 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!27 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!28 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!51 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!50)))
                                          G))
                                 (a!52 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!50)))
                                          F))
                                 (a!53 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!50)))))
                                 (a!54 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!50)))))
                                 (a!55 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!50)))))
                                 (a!69 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!68)))))
                                 (a!70 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!68)))))
                                 (a!71 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!68)))
                                          C1))
                                 (a!81 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!80)))
                                          O2))
                                 (a!82 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!80)))
                                          N2))
                                 (a!83 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!80)))))
                                 (a!84 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!80)))))
                                 (a!85 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!80)))))
                                 (a!99 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!98)))))
                                 (a!100 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!98)))))
                                 (a!101 (= (@0ContentElementScript
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!98)))
                                           K3))
                                 (a!115 (ite a!113
                                             (@3ArrayResponse (responses L3))
                                             (ite a!114
                                                  (@4ArrayResponse (responses L3))
                                                  (@defaultArrayResponse
                                                    (responses L3)))))
                                 (a!126 (and (= (blob_origin A4) Z3)
                                             (= a!12 (blob_url A4))
                                             (= (url_path a!12)
                                                (url_path_blob Z3 Y3))
                                             a!125
                                             (= a!120
                                                (SomeContentElement
                                                  (blob_celt A4)))))
                                 (a!135 (and (= (blob_origin V3) U3)
                                             (= a!12 (blob_url V3))
                                             (= (url_path a!12)
                                                (url_path_blob U3 T3))
                                             a!134
                                             (= a!120
                                                (SomeContentElement
                                                  (blob_celt V3)))))
                                 (a!145 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location N3)))
                                             a!141
                                             a!144))
                                 (a!149 (or ((_ is SSLax) (sc_same_site F4))
                                            ((_ is SSStrict) (sc_same_site F4))
                                            (and (sc_secure F4)
                                                 (= (url_protocol a!12)
                                                    ProtocolHTTPS))))
                                 (a!150 (= (@0domain (@0SomeDomain (sc_domain F4)))
                                           (@0domain (@0SomeDomain (url_host a!12)))))
                                 (a!152 (= (@1subdomain (@0SomeDomain (sc_domain F4)))
                                           (@0domain (@0SomeDomain (url_host a!12)))))
                                 (a!153 (= (@0subdomain (@0SomeDomain (sc_domain F4)))
                                           (@0subdomain (@0SomeDomain (url_host a!12)))))
                                 (a!154 (= (@1subdomain (@0SomeDomain (sc_domain F4)))
                                           (@1subdomain (@0SomeDomain (url_host a!12)))))
                                 (a!160 (and (or (not (sc_secure F4))
                                                 (= (url_protocol a!12)
                                                    ProtocolHTTPS))
                                             (sc_secure F4)
                                             (not ((_ is url_path_blob)
                                                    (url_path a!12)))
                                             (not ((_ is url_path_data)
                                                    (url_path a!12)))
                                             ((_ is SomeDomain) (url_host a!12))
                                             (= (sc_reg_domain F4)
                                                (@0SomeDomain (url_host a!12)))
                                             (= (@0url_path_res (url_path a!12))
                                                slash)
                                             (= (sc_path F4) slash)
                                             (= (sc_domain F4) NoneDomain))))
                           (let ((a!9 (ite (= (ft_correlator D4) 1)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             a!5
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history D4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history D4)))
                                           a!8))
                                 (a!32 (and a!24
                                            a!25
                                            a!26
                                            a!27
                                            a!28
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!23)))
                                            ((_ is SomeDOMElement) a!23)
                                            (= E2 N1)
                                            (= N1 S1)
                                            (= U1 H1)
                                            (= S1 T1)
                                            (= M1 T1)
                                            a!31
                                            (= F1 (DOMPath (consInt G1 K1) L1))
                                            (= B2 F1)
                                            (= Q1 (DOMPath K1 L1))
                                            (= Q1 (DOMPath nilInt R1))
                                            (= V1 O1)
                                            (= O1 P1)))
                                 (a!59 (and a!51
                                            a!52
                                            a!53
                                            a!54
                                            a!55
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!50)))
                                            ((_ is SomeDOMElement) a!50)
                                            (= P Q)
                                            (= K P)
                                            (= B1 K)
                                            (= J Q)
                                            (= R E)
                                            a!58
                                            (= C (DOMPath (consInt D H) I))
                                            (= Y C)
                                            (= N (DOMPath H I))
                                            (= N (DOMPath nilInt O))
                                            (= S L)
                                            (= L M)))
                                 (a!89 (and a!81
                                            a!82
                                            a!83
                                            a!84
                                            a!85
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!80)))
                                            ((_ is SomeDOMElement) a!80)
                                            (= Z2 M2)
                                            (= S2 X2)
                                            (= R2 Y2)
                                            (= J3 S2)
                                            (= X2 Y2)
                                            a!88
                                            (= V2 (DOMPath P2 Q2))
                                            (= V2 (DOMPath nilInt W2))
                                            (= K2 (DOMPath (consInt L2 P2) Q2))
                                            (= G3 K2)
                                            (= T2 U2)
                                            (= A3 T2)))
                                 (a!116 (ite a!111
                                             (@1ArrayResponse (responses L3))
                                             (ite a!112
                                                  (@2ArrayResponse (responses L3))
                                                  a!115)))
                                 (a!127 (or (and (= X3 J4)
                                                 (= (url_path a!12)
                                                    (url_path_data X3 W3))
                                                 (= a!120 a!123))
                                            a!126))
                                 (a!136 (or (and (= S3 J4)
                                                 (= (url_path a!12)
                                                    (url_path_data S3 R3))
                                                 (= a!120 a!132))
                                            a!135))
                                 (a!146 (= (SomeOrigin (@0SomeOrigin (rp_hd_access_control_allow_origin
                                                                       a!128)))
                                           (ite a!138 a!139 a!145)))
                                 (a!151 (and a!150
                                             ((_ is domain)
                                               (@0SomeDomain (url_host a!12)))))
                                 (a!155 (ite ((_ is domain)
                                               (@0SomeDomain (url_host a!12)))
                                             a!152
                                             (and a!153 a!154))))
                           (let ((a!10 (ite (= (ft_correlator D4) 0)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              a!5
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history D4)))
                                            a!9))
                                 (a!33 (or (and (= E2 Z1)
                                                (= Z1 A2)
                                                (= U1 A2)
                                                (= X1 (DOMPath nilInt Y1))
                                                (= B2 X1)
                                                (= V1 W1))
                                           a!32))
                                 (a!60 (or (and (= W X)
                                                (= B1 W)
                                                (= R X)
                                                (= U (DOMPath nilInt V))
                                                (= Y U)
                                                (= S T))
                                           a!59))
                                 (a!90 (or (and (= Z2 F3)
                                                (= J3 E3)
                                                (= E3 F3)
                                                (= G3 C3)
                                                (= C3 (DOMPath nilInt D3))
                                                (= A3 B3))
                                           a!89))
                                 (a!117 (= (ite a!110
                                                (@0ArrayResponse (responses L3))
                                                a!116)
                                           (ite (= C4 0)
                                                (@0ArrayResponse (responses L3))
                                                a!2)))
                                 (a!147 (ite ((_ is EmitterScript)
                                               (ft_emitter D4))
                                             (or (= a!120 NoneContentElement)
                                                 a!146)
                                             (or ((_ is EmitterWorker)
                                                   (ft_emitter D4))
                                                 ((_ is EmitterForm)
                                                   (ft_emitter D4))
                                                 a!146)))
                                 (a!156 (ite ((_ is domain)
                                               (@0SomeDomain (sc_domain F4)))
                                             a!151
                                             a!155)))
                           (let ((a!11 (= P3
                                          (Build_State (+ 1 J4)
                                                       (Build_FetchEngine
                                                         (+ 1 J4)
                                                         (ft_emitter D4)
                                                         (ft_request D4)
                                                         (ft_correlator D4)
                                                         a!4
                                                         a!10)
                                                       K4
                                                       M3
                                                       L4
                                                       M4
                                                       N4)))
                                 (a!42 (and a!33
                                            ((_ is DOMElementForm)
                                              (@0SomeDOMElement a!41))
                                            ((_ is SomeDOMElement) a!41)
                                            (= N3 E2)
                                            (= M3 U1)
                                            (= D1 F2)
                                            (= (@0DOMElementForm (@0SomeDOMElement a!41))
                                               F2)
                                            (= (ft_emitter D4)
                                               (EmitterForm E1 D1))
                                            (= E1 B2)
                                            (= B2 (DOMPath C2 (DOMIndex D2)))
                                            (= L3 V1)))
                                 (a!72 (and a!60
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!68)))
                                            a!69
                                            a!70
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!68)))
                                            ((_ is SomeDOMElement) a!68)
                                            (= N3 B1)
                                            (= M3 R)
                                            (= A C1)
                                            a!71
                                            (= (ft_emitter D4)
                                               (EmitterScript B A))
                                            (= B Y)
                                            (= Y (DOMPath Z (DOMIndex A1)))
                                            (= L3 S)))
                                 (a!105 (and a!90
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!98)))
                                             a!99
                                             a!100
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!98)))
                                             ((_ is SomeDOMElement) a!98)
                                             (= N3 J3)
                                             (= M3 Z2)
                                             (= I2 K3)
                                             a!101
                                             a!104
                                             (= (ft_emitter D4)
                                                (EmitterCORSPreflight H2 G2))
                                             (= J2 G3)
                                             (= G3 (DOMPath H3 (DOMIndex I3)))
                                             (= L3 A3)))
                                 (a!118 (and (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!107))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!107)))
                                             (= (url_protocol a!12)
                                                ProtocolHTTP)
                                             a!117))
                                 (a!119 (and (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!107))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!107)))
                                             (= (url_protocol a!12)
                                                ProtocolHTTPS)
                                             a!117))
                                 (a!148 (or ((_ is EmitterClient)
                                              (ft_emitter D4))
                                            (not ((_ is SomeOrigin)
                                                   (rp_hd_access_control_allow_origin
                                                     a!128)))
                                            a!147))
                                 (a!157 (or (not ((_ is SomeDomain)
                                                   (sc_domain F4)))
                                            a!156)))
                           (let ((a!106 (or (and (= N3 M3)
                                                 (= (ft_emitter D4)
                                                    EmitterClient))
                                            (and (= N3 M3)
                                                 (= (ft_emitter D4)
                                                    EmitterWorker))
                                            a!42
                                            a!72
                                            a!105))
                                 (a!137 (or a!118
                                            a!119
                                            (and a!127
                                                 (= (rp_hd_access_control_allow_origin
                                                      a!128)
                                                    NoneOrigin)
                                                 (= (rp_hd_location a!128)
                                                    NoneURL)
                                                 (= (url_protocol a!12)
                                                    ProtocolBlob)
                                                 (= a!129 ResponseOk)
                                                 (= (rp_hd_set_cookie a!128)
                                                    NoneSetCookie))
                                            (and a!136
                                                 (= (rp_hd_access_control_allow_origin
                                                      a!128)
                                                    NoneOrigin)
                                                 (= (rp_hd_location a!128)
                                                    NoneURL)
                                                 (= (url_protocol a!12)
                                                    ProtocolData)
                                                 (= a!129 ResponseOk)
                                                 (= (rp_hd_set_cookie a!128)
                                                    NoneSetCookie))))
                                 (a!158 (and (or (not (sc_secure F4))
                                                 (= (url_protocol a!12)
                                                    ProtocolHTTPS))
                                             a!157
                                             ((_ is SomeDomain) (url_host a!12))
                                             (= (sc_reg_domain F4)
                                                (@0SomeDomain (url_host a!12)))))
                                 (a!159 (and (or (not (sc_secure F4))
                                                 (= (url_protocol a!12)
                                                    ProtocolHTTPS))
                                             a!157
                                             (sc_secure F4)
                                             ((_ is SomeDomain) (url_host a!12))
                                             (= (sc_reg_domain F4)
                                                (@0SomeDomain (url_host a!12))))))
                           (let ((a!161 (ite ((_ is NoPrefix) (sc_name F4))
                                             a!158
                                             (ite ((_ is Secure) (sc_name F4))
                                                  a!159
                                                  a!160))))
                           (let ((a!192 (or (and (= (rp_hd_set_cookie a!128)
                                                    NoneSetCookie)
                                                 (= L4 H4))
                                            (and a!149
                                                 a!161
                                                 (= (rp_hd_set_cookie a!128)
                                                    (SomeSetCookie F4))
                                                 a!163
                                                 a!166
                                                 (= G4 a!191)))))
                           (let ((a!193 (and (Reachable L3 I4 O3)
                                             (= Q3 (consEvent a!3 I4))
                                             a!11
                                             (= O3
                                                (Build_State J4
                                                             D4
                                                             K4
                                                             M3
                                                             H4
                                                             M4
                                                             N4))
                                             (= a!12 (rq_url (ft_request D4)))
                                             a!15
                                             a!106
                                             a!137
                                             a!148
                                             a!192
                                             ((_ is NoneResponse)
                                               (ft_response D4)))))
                             (=> a!193 (Reachable L3 Q3 P3)))))))))))))
                           :weight 0))))
      (a!89 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 4))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 3))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!91 (asserted (forall ((A Script)
                               (B NestedDOMPath)
                               (C NestedDOMPath)
                               (D Int)
                               (E Window)
                               (F HTML)
                               (G Frame)
                               (H listInt)
                               (I DOMSelector)
                               (J Window)
                               (K Window)
                               (L Global)
                               (M Global)
                               (N NestedDOMPath)
                               (O DOMSelector)
                               (P Window)
                               (Q Window)
                               (R Window)
                               (S Global)
                               (T Global)
                               (U NestedDOMPath)
                               (V DOMSelector)
                               (W Window)
                               (X Window)
                               (Y NestedDOMPath)
                               (Z listInt)
                               (A1 Int)
                               (B1 Window)
                               (C1 Script)
                               (D1 Form)
                               (E1 NestedDOMPath)
                               (F1 NestedDOMPath)
                               (G1 Int)
                               (H1 Window)
                               (I1 HTML)
                               (J1 Frame)
                               (K1 listInt)
                               (L1 DOMSelector)
                               (M1 Window)
                               (N1 Window)
                               (O1 Global)
                               (P1 Global)
                               (Q1 NestedDOMPath)
                               (R1 DOMSelector)
                               (S1 Window)
                               (T1 Window)
                               (U1 Window)
                               (V1 Global)
                               (W1 Global)
                               (X1 NestedDOMPath)
                               (Y1 DOMSelector)
                               (Z1 Window)
                               (A2 Window)
                               (B2 NestedDOMPath)
                               (C2 listInt)
                               (D2 Int)
                               (E2 Window)
                               (F2 Form)
                               (G2 Request)
                               (H2 Int)
                               (I2 Script)
                               (J2 NestedDOMPath)
                               (K2 NestedDOMPath)
                               (L2 Int)
                               (M2 Window)
                               (N2 HTML)
                               (O2 Frame)
                               (P2 listInt)
                               (Q2 DOMSelector)
                               (R2 Window)
                               (S2 Window)
                               (T2 Global)
                               (U2 Global)
                               (V2 NestedDOMPath)
                               (W2 DOMSelector)
                               (X2 Window)
                               (Y2 Window)
                               (Z2 Window)
                               (A3 Global)
                               (B3 Global)
                               (C3 NestedDOMPath)
                               (D3 DOMSelector)
                               (E3 Window)
                               (F3 Window)
                               (G3 NestedDOMPath)
                               (H3 listInt)
                               (I3 Int)
                               (J3 Window)
                               (K3 Script)
                               (L3 Global)
                               (M3 Emitter)
                               (N3 Window)
                               (O3 Window)
                               (P3 State)
                               (Q3 State)
                               (R3 listEvent)
                               (S3 URL)
                               (T3 NestedDOMPath)
                               (U3 Script)
                               (V3 NestedDOMPath)
                               (W3 Form)
                               (X3 URL)
                               (Y3 Response)
                               (Z3 Int)
                               (A4 Blob)
                               (B4 Origin)
                               (C4 FetchEngine)
                               (D4 Request)
                               (E4 listEvent)
                               (F4 Int)
                               (G4 ServiceWorker)
                               (H4 ArrayoptionSetCookie)
                               (I4 ArrayoptionBlob)
                               (J4 ArrayoptionStorageItem))
                        (! (let ((a!1 (Build_State (+ 1 F4)
                                                   (Build_FetchEngine
                                                     (+ 1 F4)
                                                     M3
                                                     D4
                                                     (+ 1 (ft_correlator C4))
                                                     NoneResponse
                                                     (ft_history C4))
                                                   G4
                                                   N3
                                                   H4
                                                   I4
                                                   J4))
                                 (a!2 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (rq_url D4)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (rq_url D4)))))
                                 (a!3 (not ((_ is url_path_blob)
                                             (url_path (rq_url D4)))))
                                 (a!4 (not ((_ is url_path_data)
                                             (url_path (rq_url D4)))))
                                 (a!6 (not ((_ is SomeInt)
                                             (url_port (rq_url D4)))))
                                 (a!7 (not ((_ is SomeDomain)
                                             (url_host (rq_url D4)))))
                                 (a!11 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!12 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!13 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!14 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!15 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!16 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H1)))))
                                 (a!24 (ite (= (frame_window J1) 3)
                                            (@3ArrayWindow (windows O1))
                                            (ite (= (frame_window J1) 4)
                                                 (@4ArrayWindow (windows O1))
                                                 (@defaultArrayWindow
                                                   (windows O1)))))
                                 (a!29 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!30 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!31 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!32 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!33 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!34 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E2)))))
                                 (a!38 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!39 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!40 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!41 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!42 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!43 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                 (a!51 (ite (= (frame_window G) 3)
                                            (@3ArrayWindow (windows L))
                                            (ite (= (frame_window G) 4)
                                                 (@4ArrayWindow (windows L))
                                                 (@defaultArrayWindow
                                                   (windows L)))))
                                 (a!56 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!57 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!58 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!59 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!60 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!61 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B1)))))
                                 (a!68 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!69 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!70 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!71 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!72 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!73 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!81 (ite (= (frame_window O2) 3)
                                            (@3ArrayWindow (windows T2))
                                            (ite (= (frame_window O2) 4)
                                                 (@4ArrayWindow (windows T2))
                                                 (@defaultArrayWindow
                                                   (windows T2)))))
                                 (a!86 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!87 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!88 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!89 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!90 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!91 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J3)))))
                                 (a!97 (ite (= H2 3)
                                            (@3ArrayEmitter (emitters L3))
                                            (ite (= H2 4)
                                                 (@4ArrayEmitter (emitters L3))
                                                 (@defaultArrayEmitter
                                                   (emitters L3)))))
                                 (a!101 (not (sc_secure (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                           H4)))))
                                 (a!103 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!104 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!106 ((_ is domain)
                                          (@0SomeDomain (url_host (wd_location O3)))))
                                 (a!107 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            H4)))))
                                 (a!108 (@0domain (@0SomeDomain (url_host (wd_location O3)))))
                                 (a!109 (@0domain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!110 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!111 (@1subdomain (@0SomeDomain (url_host (wd_location O3)))))
                                 (a!113 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        H4)))))
                                 (a!114 ((_ is domain)
                                          (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!115 (@0domain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!116 (@0SomeDomain (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!117 (@1subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!118 (@0subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!122 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!124 ((_ is slash)
                                          (@0url_path_res (url_path (rq_url D4)))))
                                 (a!125 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                      H4)))))
                                 (a!126 (@0anypath (@0url_path_res (url_path (rq_url D4)))))
                                 (a!127 (@0anypath (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!129 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       H4)))))
                                 (a!131 (not (sc_secure (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                           H4)))))
                                 (a!133 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!134 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!136 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            H4)))))
                                 (a!137 (@0domain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!138 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!140 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        H4)))))
                                 (a!141 (@0SomeDomain (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!145 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!147 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                      H4)))))
                                 (a!148 (@0anypath (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!150 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       H4)))))
                                 (a!152 (not (sc_secure (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                           H4)))))
                                 (a!154 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!155 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!157 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            H4)))))
                                 (a!158 (@0domain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!159 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!161 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        H4)))))
                                 (a!162 (@0SomeDomain (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!166 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!168 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      H4)))))
                                 (a!169 (@0anypath (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!171 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       H4)))))
                                 (a!173 (not (sc_secure (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                           H4)))))
                                 (a!175 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!176 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!178 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            H4)))))
                                 (a!179 (@0domain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!180 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!182 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        H4)))))
                                 (a!183 (@0SomeDomain (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!187 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!189 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      H4)))))
                                 (a!190 (@0anypath (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!192 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       H4)))))
                                 (a!194 (not (sc_secure (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                           H4)))))
                                 (a!196 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!197 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!199 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            H4)))))
                                 (a!200 (@0domain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!201 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!203 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        H4)))))
                                 (a!204 (@0SomeDomain (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!208 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!210 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      H4)))))
                                 (a!211 (@0anypath (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                               H4)))))
                                 (a!213 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       H4)))))
                                 (a!215 (not (sc_secure (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                           H4)))))
                                 (a!217 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            H4)))
                                           SSLax))
                                 (a!218 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            H4)))
                                           SSNone))
                                 (a!220 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            H4)))))
                                 (a!221 (@0domain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!222 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                       H4)))))
                                 (a!224 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        H4)))))
                                 (a!225 (@0SomeDomain (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    H4)))))
                                 (a!229 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             H4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!231 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      H4)))))
                                 (a!232 (@0anypath (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                               H4)))))
                                 (a!234 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      H4)))
                                          (sc_value (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       H4)))))
                                 (a!239 (= (rq_hd_cookie (rq_headers D4))
                                           (Build_ArrayoptionCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping)))
                                 (a!241 (ite (= Z3 2)
                                             (@2ArrayoptionBlob I4)
                                             (ite (= Z3 3)
                                                  (@3ArrayoptionBlob I4)
                                                  (ite (= Z3 4)
                                                       (@4ArrayoptionBlob I4)
                                                       (@defaultArrayoptionBlob
                                                         I4)))))
                                 (a!244 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                           0))
                                 (a!245 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!246 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                           1))
                                 (a!247 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!248 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                           2))
                                 (a!249 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!250 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                           3))
                                 (a!251 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!252 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                           4))
                                 (a!253 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!254 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document O3)))))
                                 (a!261 (not ((_ is DOMTopLevel)
                                               (@1DOMPath (@0EmitterScript M3)))))
                                 (a!262 (and (c_earlyhtml5_form_methods
                                               (config L3))
                                             ((_ is MethodDelete)
                                               (form_method (@1EmitterForm M3)))))
                                 (a!265 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                           0))
                                 (a!266 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                           1))
                                 (a!267 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                           2))
                                 (a!268 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                           3))
                                 (a!269 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                           4))
                                 (a!272 (not ((_ is DOMTopLevel)
                                               (@1DOMPath (@0EmitterForm M3)))))
                                 (a!274 ((_ is ProtocolHTTPS)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  M3)))))
                                 (a!275 ((_ is ProtocolHTTP)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  M3)))))
                                 (a!276 (TupleOrigin (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                             M3)))
                                                     (url_host (rq_url (@1EmitterCORSPreflight
                                                                         M3)))
                                                     (url_port (rq_url (@1EmitterCORSPreflight
                                                                         M3)))))
                                 (a!277 ((_ is ProtocolData)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  M3)))))
                                 (a!278 ((_ is url_path_data)
                                          (url_path (rq_url (@1EmitterCORSPreflight
                                                              M3)))))
                                 (a!279 (@0url_path_data (url_path (rq_url (@1EmitterCORSPreflight
                                                                             M3)))))
                                 (a!280 ((_ is url_path_blob)
                                          (url_path (rq_url (@1EmitterCORSPreflight
                                                              M3)))))
                                 (a!281 (@0url_path_blob (url_path (rq_url (@1EmitterCORSPreflight
                                                                             M3)))))
                                 (a!284 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location O3)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location O3)))))
                                 (a!285 (SomeOrigin (TupleOrigin (url_protocol (wd_location O3))
                                                                 (url_host (wd_location O3))
                                                                 (url_port (wd_location O3)))))
                                 (a!286 (OpaqueOrigin (@0url_path_data (url_path (wd_location O3)))))
                                 (a!288 (SomeOrigin (@0url_path_blob (url_path (wd_location O3)))))
                                 (a!293 (not (= (rq_method (@1EmitterCORSPreflight
                                                             M3))
                                                MethodGet)))
                                 (a!294 (not (= (rq_method (@1EmitterCORSPreflight
                                                             M3))
                                                MethodPost)))
                                 (a!296 (and (= (rq_hd_origin (rq_headers D4))
                                                NoneOrigin)
                                             (= (rq_method D4) MethodGet)
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)))
                                 (a!297 (SomeOrigin (TupleOrigin (url_protocol (rq_url D4))
                                                                 (url_host (rq_url D4))
                                                                 (url_port (rq_url D4)))))
                                 (a!298 (OpaqueOrigin (@0url_path_data (url_path (rq_url D4)))))
                                 (a!300 (SomeOrigin (@0url_path_blob (url_path (rq_url D4)))))
                                 (a!304 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                4)
                                             (@4ArrayEmitter (emitters L3))
                                             (@defaultArrayEmitter
                                               (emitters L3))))
                                 (a!309 (rp_hd_access_control_allow_origin
                                          (rp_headers (@0SomeResponse (ft_response C4)))))
                                 (a!315 ((_ is SomeReferrerPolicy)
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document O3)))))
                                 (a!316 (@0SomeReferrerPolicy
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document O3)))))
                                 (a!322 (not ((_ is MethodDelete)
                                               (form_method (@1EmitterForm M3)))))
                                 (a!329 (and (or (= M3 EmitterClient)
                                                 (= M3 EmitterWorker)
                                                 (= M3 (EmitterForm V3 W3))
                                                 (= M3 (EmitterScript T3 U3)))
                                             (not (c_redirect_preflight_requests
                                                    (config L3)))))
                                 (a!331 (= (rq_hd_origin (rq_headers D4))
                                           (rq_hd_origin (rq_headers (ft_request C4)))))
                                 (a!332 ((_ is ProtocolHTTPS)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!333 ((_ is ProtocolHTTP)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!334 (TupleOrigin (url_protocol (rq_url (ft_request C4)))
                                                     (url_host (rq_url (ft_request C4)))
                                                     (url_port (rq_url (ft_request C4)))))
                                 (a!335 ((_ is ProtocolData)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!336 ((_ is url_path_data)
                                          (url_path (rq_url (ft_request C4)))))
                                 (a!337 (@0url_path_data (url_path (rq_url (ft_request C4)))))
                                 (a!338 ((_ is url_path_blob)
                                          (url_path (rq_url (ft_request C4)))))
                                 (a!339 (@0url_path_blob (url_path (rq_url (ft_request C4)))))
                                 (a!351 (consEvent (EvRequest M3
                                                              D4
                                                              (+ 1
                                                                 (ft_correlator C4)))
                                                   E4)))
                           (let ((a!5 (and a!3
                                           a!4
                                           ((_ is SomeInt)
                                             (url_port (rq_url D4)))
                                           ((_ is SomeDomain)
                                             (url_host (rq_url D4)))))
                                 (a!8 (and ((_ is url_path_data)
                                             (url_path (rq_url D4)))
                                           a!6
                                           a!7))
                                 (a!9 (and ((_ is url_path_blob)
                                             (url_path (rq_url D4)))
                                           a!4
                                           a!6
                                           a!7))
                                 (a!17 (ite (= G1 2)
                                            a!13
                                            (ite (= G1 3)
                                                 a!14
                                                 (ite (= G1 4) a!15 a!16))))
                                 (a!25 (ite (= (frame_window J1) 1)
                                            (@1ArrayWindow (windows O1))
                                            (ite (= (frame_window J1) 2)
                                                 (@2ArrayWindow (windows O1))
                                                 a!24)))
                                 (a!35 (ite (= D2 2)
                                            a!31
                                            (ite (= D2 3)
                                                 a!32
                                                 (ite (= D2 4) a!33 a!34))))
                                 (a!44 (ite (= D 2)
                                            a!40
                                            (ite (= D 3)
                                                 a!41
                                                 (ite (= D 4) a!42 a!43))))
                                 (a!52 (ite (= (frame_window G) 1)
                                            (@1ArrayWindow (windows L))
                                            (ite (= (frame_window G) 2)
                                                 (@2ArrayWindow (windows L))
                                                 a!51)))
                                 (a!62 (ite (= A1 2)
                                            a!58
                                            (ite (= A1 3)
                                                 a!59
                                                 (ite (= A1 4) a!60 a!61))))
                                 (a!74 (ite (= L2 2)
                                            a!70
                                            (ite (= L2 3)
                                                 a!71
                                                 (ite (= L2 4) a!72 a!73))))
                                 (a!82 (ite (= (frame_window O2) 1)
                                            (@1ArrayWindow (windows T2))
                                            (ite (= (frame_window O2) 2)
                                                 (@2ArrayWindow (windows T2))
                                                 a!81)))
                                 (a!92 (ite (= I3 2)
                                            a!88
                                            (ite (= I3 3)
                                                 a!89
                                                 (ite (= I3 4) a!90 a!91))))
                                 (a!98 (ite (= H2 1)
                                            (@1ArrayEmitter (emitters L3))
                                            (ite (= H2 2)
                                                 (@2ArrayEmitter (emitters L3))
                                                 a!97)))
                                 (a!102 (or a!101
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!105 (ite ((_ is EmitterClient) M3)
                                             (or a!103 a!104)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!104
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!104))))
                                 (a!119 (ite ((_ is domain) a!116)
                                             (= a!117 (@0domain a!116))
                                             (and (= a!118 (@0subdomain a!116))
                                                  (= a!117 (@1subdomain a!116)))))
                                 (a!123 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!122))
                                 (a!132 (or a!131
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!135 (ite ((_ is EmitterClient) M3)
                                             (or a!133 a!134)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!134
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!134))))
                                 (a!142 (ite ((_ is domain) a!141)
                                             (= a!117 (@0domain a!141))
                                             (and (= a!118 (@0subdomain a!141))
                                                  (= a!117 (@1subdomain a!141)))))
                                 (a!146 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!145))
                                 (a!153 (or a!152
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!156 (ite ((_ is EmitterClient) M3)
                                             (or a!154 a!155)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!155
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!155))))
                                 (a!163 (ite ((_ is domain) a!162)
                                             (= a!117 (@0domain a!162))
                                             (and (= a!118 (@0subdomain a!162))
                                                  (= a!117 (@1subdomain a!162)))))
                                 (a!167 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!166))
                                 (a!174 (or a!173
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!177 (ite ((_ is EmitterClient) M3)
                                             (or a!175 a!176)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!176
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!176))))
                                 (a!184 (ite ((_ is domain) a!183)
                                             (= a!117 (@0domain a!183))
                                             (and (= a!118 (@0subdomain a!183))
                                                  (= a!117 (@1subdomain a!183)))))
                                 (a!188 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!187))
                                 (a!195 (or a!194
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!198 (ite ((_ is EmitterClient) M3)
                                             (or a!196 a!197)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!197
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!197))))
                                 (a!205 (ite ((_ is domain) a!204)
                                             (= a!117 (@0domain a!204))
                                             (and (= a!118 (@0subdomain a!204))
                                                  (= a!117 (@1subdomain a!204)))))
                                 (a!209 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!208))
                                 (a!216 (or a!215
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!219 (ite ((_ is EmitterClient) M3)
                                             (or a!217 a!218)
                                             (ite (or ((_ is EmitterForm) M3)
                                                      ((_ is EmitterScript) M3))
                                                  a!218
                                                  (and ((_ is EmitterWorker) M3)
                                                       a!218))))
                                 (a!226 (ite ((_ is domain) a!225)
                                             (= a!117 (@0domain a!225))
                                             (and (= a!118 (@0subdomain a!225))
                                                  (= a!117 (@1subdomain a!225)))))
                                 (a!230 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!229))
                                 (a!240 (and (= M3 EmitterClient)
                                             (= (url_protocol (rq_url D4))
                                                ProtocolData)
                                             a!239))
                                 (a!242 (= (ite (= Z3 0)
                                                (@0ArrayoptionBlob I4)
                                                (ite (= Z3 1)
                                                     (@1ArrayoptionBlob I4)
                                                     a!241))
                                           (SomeBlob A4)))
                                 (a!255 (ite a!246
                                             a!247
                                             (ite a!248
                                                  a!249
                                                  (ite a!250
                                                       a!251
                                                       (ite a!252 a!253 a!254)))))
                                 (a!263 (ite ((_ is MethodPut)
                                               (form_method (@1EmitterForm M3)))
                                             (c_earlyhtml5_form_methods
                                               (config L3))
                                             a!262))
                                 (a!270 (ite a!266
                                             a!247
                                             (ite a!267
                                                  a!249
                                                  (ite a!268
                                                       a!251
                                                       (ite a!269 a!253 a!254)))))
                                 (a!282 (ite a!277
                                             (ite a!278
                                                  (SomeOrigin (OpaqueOrigin a!279))
                                                  NoneOrigin)
                                             (ite a!278
                                                  NoneOrigin
                                                  (ite a!280
                                                       (SomeOrigin a!281)
                                                       NoneOrigin))))
                                 (a!287 (ite ((_ is url_path_data)
                                               (url_path (wd_location O3)))
                                             (SomeOrigin a!286)
                                             NoneOrigin))
                                 (a!289 (ite ((_ is url_path_blob)
                                               (url_path (wd_location O3)))
                                             a!288
                                             NoneOrigin))
                                 (a!299 (ite ((_ is url_path_data)
                                               (url_path (rq_url D4)))
                                             (SomeOrigin a!298)
                                             NoneOrigin))
                                 (a!301 (ite ((_ is url_path_blob)
                                               (url_path (rq_url D4)))
                                             a!300
                                             NoneOrigin))
                                 (a!305 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                3)
                                             (@3ArrayEmitter (emitters L3))
                                             a!304))
                                 (a!310 (= (@0SomeOrigin a!309)
                                           (@0SomeOrigin (rq_hd_origin (rq_headers D4)))))
                                 (a!340 (ite a!335
                                             (ite a!336
                                                  (SomeOrigin (OpaqueOrigin a!337))
                                                  NoneOrigin)
                                             (ite a!336
                                                  NoneOrigin
                                                  (ite a!338
                                                       (SomeOrigin a!339)
                                                       NoneOrigin)))))
                           (let ((a!10 (ite ((_ is ProtocolData)
                                              (url_protocol (rq_url D4)))
                                            a!8
                                            a!9))
                                 (a!18 (ite (= G1 0)
                                            a!11
                                            (ite (= G1 1) a!12 a!17)))
                                 (a!26 (= (ite (= (frame_window J1) 0)
                                               (@0ArrayWindow (windows O1))
                                               a!25)
                                          M1))
                                 (a!36 (ite (= D2 0)
                                            a!29
                                            (ite (= D2 1) a!30 a!35)))
                                 (a!45 (ite (= D 0)
                                            a!38
                                            (ite (= D 1) a!39 a!44)))
                                 (a!53 (= (ite (= (frame_window G) 0)
                                               (@0ArrayWindow (windows L))
                                               a!52)
                                          J))
                                 (a!63 (ite (= A1 0)
                                            a!56
                                            (ite (= A1 1) a!57 a!62)))
                                 (a!75 (ite (= L2 0)
                                            a!68
                                            (ite (= L2 1) a!69 a!74)))
                                 (a!83 (= (ite (= (frame_window O2) 0)
                                               (@0ArrayWindow (windows T2))
                                               a!82)
                                          R2))
                                 (a!93 (ite (= I3 0)
                                            a!86
                                            (ite (= I3 1) a!87 a!92)))
                                 (a!99 (= (ite (= H2 0)
                                               (@0ArrayEmitter (emitters L3))
                                               a!98)
                                          (EmitterScript J2 I2)))
                                 (a!112 (or a!105
                                            (ite a!106
                                                 (ite a!107
                                                      (= a!108 a!109)
                                                      (= a!108 a!110))
                                                 (ite a!107
                                                      (= a!111 a!109)
                                                      (= a!111 a!110)))))
                                 (a!120 (ite a!114
                                             (and (= a!115 (@0domain a!116))
                                                  ((_ is domain) a!116))
                                             a!119))
                                 (a!139 (or a!135
                                            (ite a!106
                                                 (ite a!136
                                                      (= a!108 a!137)
                                                      (= a!108 a!138))
                                                 (ite a!136
                                                      (= a!111 a!137)
                                                      (= a!111 a!138)))))
                                 (a!143 (ite a!114
                                             (and (= a!115 (@0domain a!141))
                                                  ((_ is domain) a!141))
                                             a!142))
                                 (a!160 (or a!156
                                            (ite a!106
                                                 (ite a!157
                                                      (= a!108 a!158)
                                                      (= a!108 a!159))
                                                 (ite a!157
                                                      (= a!111 a!158)
                                                      (= a!111 a!159)))))
                                 (a!164 (ite a!114
                                             (and (= a!115 (@0domain a!162))
                                                  ((_ is domain) a!162))
                                             a!163))
                                 (a!181 (or a!177
                                            (ite a!106
                                                 (ite a!178
                                                      (= a!108 a!179)
                                                      (= a!108 a!180))
                                                 (ite a!178
                                                      (= a!111 a!179)
                                                      (= a!111 a!180)))))
                                 (a!185 (ite a!114
                                             (and (= a!115 (@0domain a!183))
                                                  ((_ is domain) a!183))
                                             a!184))
                                 (a!202 (or a!198
                                            (ite a!106
                                                 (ite a!199
                                                      (= a!108 a!200)
                                                      (= a!108 a!201))
                                                 (ite a!199
                                                      (= a!111 a!200)
                                                      (= a!111 a!201)))))
                                 (a!206 (ite a!114
                                             (and (= a!115 (@0domain a!204))
                                                  ((_ is domain) a!204))
                                             a!205))
                                 (a!223 (or a!219
                                            (ite a!106
                                                 (ite a!220
                                                      (= a!108 a!221)
                                                      (= a!108 a!222))
                                                 (ite a!220
                                                      (= a!111 a!221)
                                                      (= a!111 a!222)))))
                                 (a!227 (ite a!114
                                             (and (= a!115 (@0domain a!225))
                                                  ((_ is domain) a!225))
                                             a!226))
                                 (a!243 (and (= M3 EmitterClient)
                                             (= (blob_origin A4) B4)
                                             (= (rq_url D4) (blob_url A4))
                                             (= (url_protocol (rq_url D4))
                                                ProtocolBlob)
                                             a!239
                                             (= (url_path (rq_url D4))
                                                (url_path_blob B4 Z3))
                                             a!242))
                                 (a!256 ((_ is ContentElementScript)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!244
                                                                   a!245
                                                                   a!255)))))
                                 (a!257 ((_ is ContentElementImage)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!244
                                                                   a!245
                                                                   a!255)))))
                                 (a!258 ((_ is ContentElementHTML)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!244
                                                                   a!245
                                                                   a!255)))))
                                 (a!259 (not ((_ is DOMElementForm)
                                               (@0SomeDOMElement (ite a!244
                                                                      a!245
                                                                      a!255)))))
                                 (a!260 (@0ContentElementScript
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!244
                                                                   a!245
                                                                   a!255)))))
                                 (a!264 (or ((_ is MethodPost)
                                              (form_method (@1EmitterForm M3)))
                                            ((_ is MethodGet)
                                              (form_method (@1EmitterForm M3)))
                                            a!263))
                                 (a!271 (= (@0DOMElementForm (@0SomeDOMElement (ite a!265
                                                                                    a!245
                                                                                    a!270)))
                                           (@1EmitterForm M3)))
                                 (a!283 (not (= (ite (or a!274 a!275)
                                                     (SomeOrigin a!276)
                                                     a!282)
                                                NoneOrigin)))
                                 (a!290 (ite ((_ is url_path_data)
                                               (url_path (wd_location O3)))
                                             NoneOrigin
                                             a!289))
                                 (a!302 (ite ((_ is url_path_data)
                                               (url_path (rq_url D4)))
                                             NoneOrigin
                                             a!301))
                                 (a!306 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                2)
                                             (@2ArrayEmitter (emitters L3))
                                             a!305)))
                           (let ((a!19 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!18)))
                                          J1))
                                 (a!20 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!18)))
                                          I1))
                                 (a!21 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!18)))))
                                 (a!22 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!18)))))
                                 (a!23 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!18)))))
                                 (a!46 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!45)))
                                          G))
                                 (a!47 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!45)))
                                          F))
                                 (a!48 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!45)))))
                                 (a!49 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!45)))))
                                 (a!50 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!45)))))
                                 (a!64 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!63)))))
                                 (a!65 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!63)))))
                                 (a!66 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!63)))
                                          C1))
                                 (a!76 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!75)))
                                          O2))
                                 (a!77 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!75)))
                                          N2))
                                 (a!78 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!75)))))
                                 (a!79 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!75)))))
                                 (a!80 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!75)))))
                                 (a!94 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!93)))))
                                 (a!95 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!93)))))
                                 (a!96 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!93)))
                                          K3))
                                 (a!121 (and a!120
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!144 (and a!143
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!165 (and a!164
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!186 (and a!185
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!207 (and a!206
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!228 (and a!227
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!273 (and a!264
                                             ((_ is DOMElementForm)
                                               (@0SomeDOMElement (ite a!265
                                                                      a!245
                                                                      a!270)))
                                             ((_ is SomeDOMElement)
                                               (ite a!265 a!245 a!270))
                                             a!271
                                             a!272))
                                 (a!291 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location O3)))
                                             a!287
                                             a!290))
                                 (a!303 (ite ((_ is ProtocolData)
                                               (url_protocol (rq_url D4)))
                                             a!299
                                             a!302))
                                 (a!307 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                1)
                                             (@1ArrayEmitter (emitters L3))
                                             a!306)))
                           (let ((a!27 (and a!19
                                            a!20
                                            a!21
                                            a!22
                                            a!23
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!18)))
                                            ((_ is SomeDOMElement) a!18)
                                            (= S1 T1)
                                            (= M1 T1)
                                            (= E2 N1)
                                            (= N1 S1)
                                            (= U1 H1)
                                            a!26
                                            (= B2 F1)
                                            (= Q1 (DOMPath K1 L1))
                                            (= Q1 (DOMPath nilInt R1))
                                            (= F1 (DOMPath (consInt G1 K1) L1))
                                            (= O1 P1)
                                            (= V1 O1)))
                                 (a!54 (and a!46
                                            a!47
                                            a!48
                                            a!49
                                            a!50
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!45)))
                                            ((_ is SomeDOMElement) a!45)
                                            (= R E)
                                            (= P Q)
                                            (= J Q)
                                            (= B1 K)
                                            (= K P)
                                            a!53
                                            (= C (DOMPath (consInt D H) I))
                                            (= Y C)
                                            (= N (DOMPath H I))
                                            (= N (DOMPath nilInt O))
                                            (= S L)
                                            (= L M)))
                                 (a!84 (and a!76
                                            a!77
                                            a!78
                                            a!79
                                            a!80
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!75)))
                                            ((_ is SomeDOMElement) a!75)
                                            (= Z2 M2)
                                            (= J3 S2)
                                            (= X2 Y2)
                                            (= S2 X2)
                                            (= R2 Y2)
                                            a!83
                                            (= K2 (DOMPath (consInt L2 P2) Q2))
                                            (= V2 (DOMPath P2 Q2))
                                            (= V2 (DOMPath nilInt W2))
                                            (= G3 K2)
                                            (= A3 T2)
                                            (= T2 U2)))
                                 (a!128 (and a!102
                                             a!112
                                             (ite a!113 a!121 a!123)
                                             (ite a!124
                                                  a!125
                                                  (or a!125 (= a!126 a!127)))
                                             a!3
                                             a!4))
                                 (a!149 (and a!132
                                             a!139
                                             (ite a!140 a!144 a!146)
                                             (ite a!124
                                                  a!147
                                                  (or a!147 (= a!126 a!148)))
                                             a!3
                                             a!4))
                                 (a!170 (and a!153
                                             a!160
                                             (ite a!161 a!165 a!167)
                                             (ite a!124
                                                  a!168
                                                  (or a!168 (= a!126 a!169)))
                                             a!3
                                             a!4))
                                 (a!191 (and a!174
                                             a!181
                                             (ite a!182 a!186 a!188)
                                             (ite a!124
                                                  a!189
                                                  (or a!189 (= a!126 a!190)))
                                             a!3
                                             a!4))
                                 (a!212 (and a!195
                                             a!202
                                             (ite a!203 a!207 a!209)
                                             (ite a!124
                                                  a!210
                                                  (or a!210 (= a!126 a!211)))
                                             a!3
                                             a!4))
                                 (a!233 (and a!216
                                             a!223
                                             (ite a!224 a!228 a!230)
                                             (ite a!124
                                                  a!231
                                                  (or a!231 (= a!126 a!232)))
                                             a!3
                                             a!4))
                                 (a!292 (not (= (ite (or a!274 a!275)
                                                     (SomeOrigin a!276)
                                                     a!282)
                                                (ite a!284 a!285 a!291))))
                                 (a!308 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                0)
                                             (@0ArrayEmitter (emitters L3))
                                             a!307))
                                 (a!313 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!284
                                                                  a!285
                                                                  a!291)))
                                             (ite a!284 a!285 a!291)
                                             NoneOrigin))
                                 (a!317 (Build_URL (@0TupleOrigin (@0SomeOrigin (ite a!284
                                                                                     a!285
                                                                                     a!291)))
                                                   (@1TupleOrigin (@0SomeOrigin (ite a!284
                                                                                     a!285
                                                                                     a!291)))
                                                   (@2TupleOrigin (@0SomeOrigin (ite a!284
                                                                                     a!285
                                                                                     a!291)))
                                                   (url_path_res slash)))
                                 (a!321 (and (c_earlyhtml5_form_methods
                                               (config L3))
                                             (not (= (ite a!2 a!297 a!303)
                                                     NoneOrigin))
                                             (= (ite a!2 a!297 a!303)
                                                (ite a!284 a!285 a!291))))
                                 (a!341 (= (ite a!2 a!297 a!303)
                                           (ite (or a!332 a!333)
                                                (SomeOrigin a!334)
                                                a!340))))
                           (let ((a!28 (or (and (= E2 Z1)
                                                (= Z1 A2)
                                                (= U1 A2)
                                                (= B2 X1)
                                                (= X1 (DOMPath nilInt Y1))
                                                (= V1 W1))
                                           a!27))
                                 (a!55 (or (and (= R X)
                                                (= B1 W)
                                                (= W X)
                                                (= Y U)
                                                (= U (DOMPath nilInt V))
                                                (= S T))
                                           a!54))
                                 (a!85 (or (and (= Z2 F3)
                                                (= J3 E3)
                                                (= E3 F3)
                                                (= G3 C3)
                                                (= C3 (DOMPath nilInt D3))
                                                (= A3 B3))
                                           a!84))
                                 (a!130 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!128
                                                  (SomeCookieMapping a!129)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!151 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!149
                                                  (SomeCookieMapping a!150)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!172 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!170
                                                  (SomeCookieMapping a!171)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!193 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!191
                                                  (SomeCookieMapping a!192)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!214 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!212
                                                  (SomeCookieMapping a!213)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!235 (ite ((_ is SomeDomain)
                                               (url_host (wd_location O3)))
                                             (ite a!233
                                                  (SomeCookieMapping a!234)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!295 (ite ((_ is EmitterScript) M3)
                                             (and a!256
                                                  (not a!257)
                                                  (not a!258)
                                                  a!259
                                                  ((_ is SomeDOMElement)
                                                    (ite a!244 a!245 a!255))
                                                  (= a!260 (@1EmitterScript M3))
                                                  a!261)
                                             (ite ((_ is EmitterForm) M3)
                                                  a!273
                                                  (or ((_ is EmitterWorker) M3)
                                                      (and a!283
                                                           a!292
                                                           a!293
                                                           a!294)))))
                                 (a!311 (and (= M3 a!308)
                                             (not ((_ is EmitterWorker)
                                                    (ft_emitter C4)))
                                             (not ((_ is EmitterForm)
                                                    (ft_emitter C4)))
                                             (not ((_ is EmitterScript)
                                                    (ft_emitter C4)))
                                             (not ((_ is EmitterClient)
                                                    (ft_emitter C4)))
                                             ((_ is SomeOrigin) a!309)
                                             ((_ is SomeOrigin)
                                               (rq_hd_origin (rq_headers D4)))
                                             (= D4
                                                (@1EmitterCORSPreflight
                                                  (ft_emitter C4)))
                                             a!310
                                             ((_ is SomeResponse)
                                               (ft_response C4))))
                                 (a!314 (= (rq_hd_origin (rq_headers D4))
                                           (ite ((_ is SomeOrigin)
                                                  (ite a!284 a!285 a!291))
                                                a!313
                                                (ite a!284 a!285 a!291))))
                                 (a!318 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!284
                                                                  a!285
                                                                  a!291)))
                                             (SomeURL a!317)
                                             NoneURL))
                                 (a!323 (ite ((_ is MethodPut)
                                               (form_method (@1EmitterForm M3)))
                                             a!321
                                             (or a!321 a!322)))
                                 (a!342 (and (= (rq_hd_origin (rq_headers D4))
                                                NoneOrigin)
                                             (not a!341))))
                           (let ((a!37 (and a!28
                                            ((_ is DOMElementForm)
                                              (@0SomeDOMElement a!36))
                                            ((_ is SomeDOMElement) a!36)
                                            (= N3 U1)
                                            (= O3 E2)
                                            (= D1 F2)
                                            (= (@0DOMElementForm (@0SomeDOMElement a!36))
                                               F2)
                                            (= M3 (EmitterForm E1 D1))
                                            (= B2 (DOMPath C2 (DOMIndex D2)))
                                            (= E1 B2)
                                            (= L3 V1)))
                                 (a!67 (and a!55
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!63)))
                                            a!64
                                            a!65
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!63)))
                                            ((_ is SomeDOMElement) a!63)
                                            (= N3 R)
                                            (= O3 B1)
                                            (= A C1)
                                            a!66
                                            (= M3 (EmitterScript B A))
                                            (= B Y)
                                            (= Y (DOMPath Z (DOMIndex A1)))
                                            (= L3 S)))
                                 (a!100 (and a!85
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!93)))
                                             a!94
                                             a!95
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!93)))
                                             ((_ is SomeDOMElement) a!93)
                                             (= N3 Z2)
                                             (= O3 J3)
                                             (= I2 K3)
                                             a!96
                                             (= M3 (EmitterCORSPreflight H2 G2))
                                             a!99
                                             (= G3 (DOMPath H3 (DOMIndex I3)))
                                             (= J2 G3)
                                             (= L3 A3)))
                                 (a!236 (Build_ArrayoptionCookieMapping
                                          (ite ((_ is SomeSetCookie)
                                                 (@0ArrayoptionSetCookie H4))
                                               a!130
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@1ArrayoptionSetCookie H4))
                                               a!151
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@2ArrayoptionSetCookie H4))
                                               a!172
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@3ArrayoptionSetCookie H4))
                                               a!193
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@4ArrayoptionSetCookie H4))
                                               a!214
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@defaultArrayoptionSetCookie
                                                   H4))
                                               a!235
                                               NoneCookieMapping)))
                                 (a!312 (or (= (rq_method D4) MethodGet)
                                            (= (rq_method D4) MethodPost)
                                            (= (ite a!2 a!297 a!303)
                                               (ite a!284 a!285 a!291))
                                            (= (ite a!2 a!297 a!303) NoneOrigin)
                                            a!311))
                                 (a!319 (ite ((_ is ReferrerPolicyNoReferrer)
                                               a!316)
                                             NoneURL
                                             (ite ((_ is SomeOrigin)
                                                    (ite a!284 a!285 a!291))
                                                  a!318
                                                  NoneURL)))
                                 (a!324 (or ((_ is MethodPost)
                                              (form_method (@1EmitterForm M3)))
                                            ((_ is MethodGet)
                                              (form_method (@1EmitterForm M3)))
                                            a!323))
                                 (a!343 (and (or (and a!331 a!341) a!342)
                                             (not (c_origin_header_on_cross_origin_redirect
                                                    (config L3))))))
                           (let ((a!237 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTP)
                                             (= (rq_hd_cookie (rq_headers D4))
                                                a!236)))
                                 (a!238 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)
                                             (= (rq_hd_cookie (rq_headers D4))
                                                a!236)))
                                 (a!320 (and a!312
                                             a!314
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!315 a!319 NoneURL))))
                                 (a!325 (and a!324
                                             a!314
                                             (= (rq_method D4)
                                                (form_method (@1EmitterForm M3)))
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!315 a!319 NoneURL))
                                             (= (rq_url D4)
                                                (form_action (@1EmitterForm M3)))))
                                 (a!326 (and a!312
                                             a!314
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)))
                                 (a!327 (and a!314
                                             (not (= (ite a!2 a!297 a!303)
                                                     NoneOrigin))
                                             (not (= (ite a!2 a!297 a!303)
                                                     (ite a!284 a!285 a!291)))
                                             (= (rq_method D4) MethodOptions)
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!315 a!319 NoneURL))
                                             (= (rq_url D4)
                                                (rq_url (@1EmitterCORSPreflight
                                                          M3)))))
                                 (a!344 (or (and (c_origin_header_on_cross_origin_redirect
                                                   (config L3))
                                                 a!331)
                                            a!343)))
                           (let ((a!328 (ite ((_ is EmitterScript) M3)
                                             a!320
                                             (ite ((_ is EmitterForm) M3)
                                                  a!325
                                                  (ite ((_ is EmitterWorker) M3)
                                                       a!326
                                                       a!327))))
                                 (a!345 (and a!344
                                             (= (ft_emitter C4) M3)
                                             (= (rq_method D4) MethodGet)
                                             (= (rp_hd_location (rp_headers Y3))
                                                (SomeURL S3))
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)
                                             (= (rq_url D4) S3)
                                             (= (rq_body D4) NoneInt)))
                                 (a!347 (and a!344
                                             (= (ft_emitter C4) M3)
                                             (= (rq_method D4)
                                                (rq_method (ft_request C4)))
                                             (= (rp_hd_location (rp_headers Y3))
                                                (SomeURL X3))
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)
                                             (= (rq_url D4) X3)
                                             (= (rq_body D4)
                                                (rq_body (ft_request C4))))))
                           (let ((a!330 (and (ite ((_ is EmitterClient) M3)
                                                  a!296
                                                  a!328)
                                             (= (rp_hd_location (rp_headers Y3))
                                                NoneURL))))
                           (let ((a!346 (and (or (c_redirect_preflight_requests
                                                   (config L3))
                                                 a!329)
                                             (or a!330 a!345)
                                             (= (rp_code Y3) ResponseFound)))
                                 (a!348 (and (or (c_redirect_preflight_requests
                                                   (config L3))
                                                 a!329)
                                             (or a!330 a!347)
                                             (= (rp_code Y3)
                                                ResponseTemporaryRedirect))))
                           (let ((a!349 (or (and (ite ((_ is EmitterClient) M3)
                                                      a!296
                                                      a!328)
                                                 (= (rp_code Y3) ResponseOk))
                                            (and (ite ((_ is EmitterClient) M3)
                                                      a!296
                                                      a!328)
                                                 (= (rp_code Y3)
                                                    ResponseNoContent))
                                            a!346
                                            a!348)))
                           (let ((a!350 (or (and a!349
                                                 (= (ft_response C4)
                                                    (SomeResponse Y3)))
                                            (and (ite ((_ is EmitterClient) M3)
                                                      a!296
                                                      a!328)
                                                 (= (ft_response C4)
                                                    NoneResponse)))))
                           (let ((a!352 (and (Reachable L3 E4 P3)
                                             (= P3
                                                (Build_State F4
                                                             C4
                                                             G4
                                                             N3
                                                             H4
                                                             I4
                                                             J4))
                                             (= Q3 a!1)
                                             (ite a!2 a!5 a!10)
                                             (or (and (= O3 N3)
                                                      (= M3 EmitterClient))
                                                 (and (= O3 N3)
                                                      (= M3 EmitterWorker))
                                                 a!37
                                                 a!67
                                                 a!100)
                                             (or a!237 a!238 a!240 a!243)
                                             (or ((_ is EmitterClient) M3)
                                                 a!295)
                                             a!350
                                             (= R3 a!351))))
                             (=> a!352 (Reachable L3 R3 Q3))))))))))))))))
                           :weight 0))))
      (a!96 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 4))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!102 (Build_Window 0
                           NoneInt
                           (Build_URL ProtocolHTTP
                                      (SomeDomain (domain 0))
                                      (SomeInt 0)
                                      (url_path_res slash))
                           NoneDomain
                           (Build_Document 0
                                           0
                                           (Build_ResponseHeaders
                                             NoneContentType
                                             NoneSetCookie
                                             NoneOrigin
                                             NoneURL
                                             NoneCSP
                                             NoneReferrerPolicy)
                                           (Build_HTML 0
                                                       0
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement))
                                           (Build_DOM 0
                                                      0
                                                      (Build_ArrayoptionDOMElement
                                                        NoneDOMElement
                                                        NoneDOMElement
                                                        NoneDOMElement
                                                        NoneDOMElement
                                                        NoneDOMElement
                                                        NoneDOMElement))
                                           (Build_Initiators NoneInt
                                                             (Build_ArrayoptionInt
                                                               NoneInt
                                                               NoneInt
                                                               NoneInt
                                                               NoneInt
                                                               NoneInt
                                                               NoneInt)))))
      (a!109 (asserted (forall ((A Global))
                         (! (let ((a!1 (distinct (@0pairOriginoptionCSP
                                                   (@0ArrayprodOriginoptionCSP
                                                     (origin_csp A)))
                                                 (@0pairOriginoptionCSP
                                                   (@1ArrayprodOriginoptionCSP
                                                     (origin_csp A)))
                                                 (@0pairOriginoptionCSP
                                                   (@2ArrayprodOriginoptionCSP
                                                     (origin_csp A)))
                                                 (@0pairOriginoptionCSP
                                                   (@3ArrayprodOriginoptionCSP
                                                     (origin_csp A)))
                                                 (@0pairOriginoptionCSP
                                                   (@4ArrayprodOriginoptionCSP
                                                     (origin_csp A)))
                                                 (@0pairOriginoptionCSP
                                                   (@defaultArrayprodOriginoptionCSP
                                                     (origin_csp A)))))
                                  (a!2 (pairOriginoptionCSP
                                         (TupleOrigin ProtocolHTTP
                                                      (SomeDomain (domain 0))
                                                      (SomeInt 0))
                                         NoneCSP))
                                  (a!4 (Build_RequestHeaders
                                         NoneOrigin
                                         (Build_ArrayoptionCookieMapping
                                           NoneCookieMapping
                                           NoneCookieMapping
                                           NoneCookieMapping
                                           NoneCookieMapping
                                           NoneCookieMapping
                                           NoneCookieMapping)
                                         NoneURL))
                                  (a!6 (Build_Window 0
                                                     NoneInt
                                                     (Build_URL ProtocolHTTP
                                                                (SomeDomain (domain 0))
                                                                (SomeInt 0)
                                                                (url_path_res slash))
                                                     NoneDomain
                                                     (Build_Document 0
                                                                     0
                                                                     (Build_ResponseHeaders
                                                                       NoneContentType
                                                                       NoneSetCookie
                                                                       NoneOrigin
                                                                       NoneURL
                                                                       NoneCSP
                                                                       NoneReferrerPolicy)
                                                                     (Build_HTML 0
                                                                                 0
                                                                                 (Build_ArrayoptionHTMLElement
                                                                                   NoneHTMLElement
                                                                                   NoneHTMLElement
                                                                                   NoneHTMLElement
                                                                                   NoneHTMLElement
                                                                                   NoneHTMLElement
                                                                                   NoneHTMLElement))
                                                                     (Build_DOM 0
                                                                                0
                                                                                (Build_ArrayoptionDOMElement
                                                                                  NoneDOMElement
                                                                                  NoneDOMElement
                                                                                  NoneDOMElement
                                                                                  NoneDOMElement
                                                                                  NoneDOMElement
                                                                                  NoneDOMElement))
                                                                     (Build_Initiators NoneInt
                                                                                       (Build_ArrayoptionInt
                                                                                         NoneInt
                                                                                         NoneInt
                                                                                         NoneInt
                                                                                         NoneInt
                                                                                         NoneInt
                                                                                         NoneInt))))))
                            (let ((a!3 (and a!1
                                            (distinct (@0ArrayResponse (responses A))
                                                      (@1ArrayResponse (responses A))
                                                      (@2ArrayResponse (responses A))
                                                      (@3ArrayResponse (responses A))
                                                      (@4ArrayResponse (responses A))
                                                      (@defaultArrayResponse
                                                        (responses A)))
                                            (distinct (@0ArrayRequest (requests A))
                                                      (@1ArrayRequest (requests A))
                                                      (@2ArrayRequest (requests A))
                                                      (@3ArrayRequest (requests A))
                                                      (@4ArrayRequest (requests A))
                                                      (@defaultArrayRequest
                                                        (requests A)))
                                            (= (@0ArrayprodOriginoptionCSP
                                                 (origin_csp A))
                                               a!2)))
                                  (a!5 (Build_Request MethodGet
                                                      (Build_URL ProtocolHTTP
                                                                 (SomeDomain (domain 0))
                                                                 (SomeInt 0)
                                                                 (url_path_res slash))
                                                      a!4
                                                      NoneInt)))
                            (let ((a!7 (Build_State 0
                                                    (Build_FetchEngine
                                                      0
                                                      EmitterClient
                                                      a!5
                                                      0
                                                      NoneResponse
                                                      (Build_ArrayoptionprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt
                                                        NoneprodprodEmitterIntInt))
                                                    (Build_ServiceWorker
                                                      0
                                                      (Build_ArrayoptionInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt))
                                                    a!6
                                                    (Build_ArrayoptionSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie)
                                                    (Build_ArrayoptionBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob)
                                                    (Build_ArrayoptionStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem))))
                              (=> a!3 (Reachable A nilEvent a!7)))))
                            :weight 0)))))
(let ((a!2 (hyper-res a!1
                      (forall ((A Global)
                               (B NestedDOMPath)
                               (C Bool)
                               (D Bool)
                               (E Window)
                               (F Bool)
                               (G Bool)
                               (H Bool)
                               (I NestedDOMPath)
                               (J Bool)
                               (K Bool)
                               (L HTML)
                               (M Bool)
                               (N Bool)
                               (O Bool)
                               (P Bool)
                               (Q Window)
                               (R Bool)
                               (S Global)
                               (T NestedDOMPath)
                               (U Bool)
                               (V Window)
                               (W Bool)
                               (X Bool)
                               (Y Bool)
                               (Z Bool)
                               (A1 Bool)
                               (B1 Bool)
                               (C1 Bool)
                               (D1 Bool)
                               (E1 Bool)
                               (F1 Bool)
                               (G1 Bool)
                               (H1 Bool)
                               (I1 Bool)
                               (J1 Bool)
                               (K1 Bool)
                               (L1 Bool)
                               (M1 Bool)
                               (N1 Bool)
                               (O1 Bool)
                               (P1 Bool)
                               (Q1 Bool))
                        (! (let ((a!1 (Build_URL ProtocolHTTPS
                                                 (SomeDomain (domain 3143))
                                                 (SomeInt 34522)
                                                 (url_path_res (anypath 212))))
                                 (a!2 (Build_RequestHeaders
                                        NoneOrigin
                                        (Build_ArrayoptionCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping)
                                        NoneURL))
                                 (a!3 (Build_URL ProtocolHTTPS
                                                 (SomeDomain (domain 3143))
                                                 (SomeInt 34522)
                                                 (url_path_res (anypath 8214))))
                                 (a!4 (Build_ArrayoptionCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        (SomeCookieMapping
                                          (Build_CookieMapping
                                            (Secure 76081)
                                            8213))
                                        NoneCookieMapping
                                        NoneCookieMapping))
                                 (a!5 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 19153
                                                                        19154))
                                                 (SomeInt 34826)
                                                 (url_path_res (anypath 76072))))
                                 (a!7 (SomeTrustedTypes (Build_TrustedTypes
                                                          (SomeoptionInt (SomeInt 27503))
                                                          true)))
                                 (a!9 (SomeContentElement
                                        (ContentElementHTML
                                          (Build_HTML 76116
                                                      76115
                                                      (Build_ArrayoptionHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement)))))
                                 (a!11 (SomeSetCookie (Build_SetCookie (NoPrefix 76114)
                                                                       19152
                                                                       (SomeDomain (subdomain 19153
                                                                                              19154))
                                                                       (subdomain 19153
                                                                                  19154)
                                                                       (anypath 76113)
                                                                       false
                                                                       false
                                                                       SSStrict)))
                                 (a!12 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                                           (SomeTrustedTypes (Build_TrustedTypes
                                                                               NoneoptionInt
                                                                               false)))))
                                 (a!15 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 76109)
                                                                         76108
                                                                         NoneDomain
                                                                         (domain 76107)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 76106))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 27542)
                                                             (url_path_data 76105
                                                                            76104)))
                                         (SomeCSP (Build_CSP NoneCSPSrc
                                                             NoneTrustedTypes))
                                         NoneReferrerPolicy))
                                 (a!16 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 76103
                                                       76102
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!18 (SomeTrustedTypes (Build_TrustedTypes
                                                           (SomeoptionInt (SomeInt 34339))
                                                           false)))
                                 (a!21 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 49941)
                                                                             (url_path_data 76074
                                                                                            76073)))))
                                 (a!22 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 49939)
                                                                             (url_path_data 76071
                                                                                            76070)))))
                                 (a!23 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 49938)
                                                                             (url_path_data 76069
                                                                                            76068)))))
                                 (a!24 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 49937)
                                                                             (url_path_data 76067
                                                                                            76066)))))
                                 (a!27 (SomeSetCookie (Build_SetCookie (Secure 76081)
                                                                       8213
                                                                       (SomeDomain (domain 3143))
                                                                       (domain 3143)
                                                                       (anypath 8214)
                                                                       true
                                                                       false
                                                                       SSStrict)))
                                 (a!28 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                 (SomeoptionInt (SomeInt 27998))
                                                                 13861
                                                                 NoneInt
                                                                 NonePath)))
                                 (a!31 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 28533)
                                                                              (url_path_data 76078
                                                                                             76077)))))
                                 (a!32 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 61136)
                                                                             (url_path_data 76065
                                                                                            76064)))))
                                 (a!33 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 28534)
                                                                              (url_path_data 76076
                                                                                             76075)))))
                                 (a!34 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 61134)
                                                                             (url_path_data 76063
                                                                                            76062)))))
                                 (a!35 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 61133)
                                                                             (url_path_data 76061
                                                                                            76060)))))
                                 (a!37 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 76098)
                                                                         76097
                                                                         NoneDomain
                                                                         (domain 76096)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 27541)
                                                             (url_path_data 76095
                                                                            76094)))
                                         (SomeCSP (Build_CSP NoneCSPSrc
                                                             NoneTrustedTypes))
                                         NoneReferrerPolicy))
                                 (a!38 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 76093
                                                       76092
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!41 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 26105)
                                                                               (url_path_data 76091
                                                                                              76090))
                                                                    76089)))
                                 (a!42 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 26032)
                                                                               (url_path_data 76088
                                                                                              76087))
                                                                    76086)))
                                 (a!43 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 26260)
                                                                               (url_path_data 76085
                                                                                              76084))
                                                                    76083)))
                                 (a!44 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 49941)
                                                                              (url_path_data 76074
                                                                                             76073)))))
                                 (a!46 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 49939)
                                                                              (url_path_data 76071
                                                                                             76070)))))
                                 (a!47 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 49938)
                                                                              (url_path_data 76069
                                                                                             76068)))))
                                 (a!48 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 49937)
                                                                              (url_path_data 76067
                                                                                             76066)))))
                                 (a!50 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 61136)
                                                                              (url_path_data 76065
                                                                                             76064)))))
                                 (a!51 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 61134)
                                                                              (url_path_data 76063
                                                                                             76062)))))
                                 (a!52 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 61133)
                                                                              (url_path_data 76061
                                                                                             76060)))))
                                 (a!57 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 25615)
                                                                              (url_path_data 76056
                                                                                             76055)))))
                                 (a!60 (Build_Document 23984
                                                       23985
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 23980
                                                                   23981
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 23982
                                                                  23983
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 35771)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 35777)
                                                                           (SomeInt 35776)
                                                                           (SomeInt 35775)
                                                                           (SomeInt 35774)
                                                                           (SomeInt 35773)
                                                                           (SomeInt 35772)))))
                                 (a!62 (Build_ArrayContentElement
                                         (ContentElementHTML
                                           (Build_HTML 76052
                                                       76051
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 76050
                                                       76049
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 76048
                                                       76047
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 76046
                                                       76045
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 76044
                                                       76043
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 76042
                                                       76041
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!63 (pairOriginoptionCSP
                                         (TupleOrigin ProtocolHTTP
                                                      (SomeDomain (domain 0))
                                                      (SomeInt 0))
                                         NoneCSP))
                                 (a!74 (Build_ArrayoptionprodprodEmitterIntInt
                                         NoneprodprodEmitterIntInt
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 0)
                                             4))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 1)
                                             3))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient
                                                             18951)
                                             1))
                                         NoneprodprodEmitterIntInt
                                         NoneprodprodEmitterIntInt))
                                 (a!76 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 34825)
                                                                             (url_path_data 94421
                                                                                            94420)))))
                                 (a!78 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34825)
                                                                              (url_path_data 94421
                                                                                             94420)))))
                                 (a!85 (ContentElementFrame
                                         (Build_Frame (Build_URL ProtocolHTTP
                                                                 NoneDomain
                                                                 (SomeInt 24888)
                                                                 (url_path_data 94408
                                                                                94407))
                                                      94406)
                                         (Build_HTML 94405
                                                     94404
                                                     (Build_ArrayoptionHTMLElement
                                                       NoneHTMLElement
                                                       NoneHTMLElement
                                                       NoneHTMLElement
                                                       NoneHTMLElement
                                                       NoneHTMLElement
                                                       NoneHTMLElement))))
                                 (a!87 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 26884)
                                                                              (url_path_data 94403
                                                                                             94402)))))
                                 (a!88 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 26757)
                                                                              (url_path_data 94401
                                                                                             94400)))))
                                 (a!99 (Build_Frame (Build_URL ProtocolHTTP
                                                               NoneDomain
                                                               (SomeInt 28607)
                                                               (url_path_data 107087
                                                                              107088))
                                                    105086))
                                 (a!105 (ContentElementFrame
                                          (Build_Frame (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 25214)
                                                                  (url_path_data 101055
                                                                                 101054))
                                                       101053)
                                          (Build_HTML 101052
                                                      101051
                                                      (Build_ArrayoptionHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement))))
                                 (a!107 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 26588)
                                                                               (url_path_data 101050
                                                                                              101049)))))
                                 (a!108 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 26534)
                                                                               (url_path_data 101048
                                                                                              101047)))))
                                 (a!109 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 25924)
                                                                               (url_path_data 101046
                                                                                              101045)))))
                                 (a!114 (Build_ArrayResponse
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28594)
                                                                     (url_path_data 69819
                                                                                    69818))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28593)
                                                                     (url_path_data 69817
                                                                                    69816))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28592)
                                                                     (url_path_data 69815
                                                                                    69814))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28591)
                                                                     (url_path_data 69813
                                                                                    69812))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28590)
                                                                     (url_path_data 69811
                                                                                    69810))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28589)
                                                                     (url_path_data 69809
                                                                                    69808))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)))
                                 (a!115 (Build_Document 69798
                                                        69797
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69796
                                                                    69795
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69794
                                                                   69793
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28581)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28587)
                                                                            (SomeInt 28586)
                                                                            (SomeInt 28585)
                                                                            (SomeInt 28584)
                                                                            (SomeInt 28583)
                                                                            (SomeInt 28582)))))
                                 (a!116 (Build_Document 69789
                                                        69788
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69787
                                                                    69786
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69785
                                                                   69784
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28572)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28578)
                                                                            (SomeInt 28577)
                                                                            (SomeInt 28576)
                                                                            (SomeInt 28575)
                                                                            (SomeInt 28574)
                                                                            (SomeInt 28573)))))
                                 (a!117 (Build_Document 69780
                                                        69779
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69778
                                                                    69777
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69776
                                                                   69775
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28563)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28569)
                                                                            (SomeInt 28568)
                                                                            (SomeInt 28567)
                                                                            (SomeInt 28566)
                                                                            (SomeInt 28565)
                                                                            (SomeInt 28564)))))
                                 (a!118 (Build_Document 69771
                                                        69770
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69769
                                                                    69768
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69767
                                                                   69766
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28554)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28560)
                                                                            (SomeInt 28559)
                                                                            (SomeInt 28558)
                                                                            (SomeInt 28557)
                                                                            (SomeInt 28556)
                                                                            (SomeInt 28555)))))
                                 (a!119 (Build_Document 69762
                                                        69761
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69760
                                                                    69759
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69758
                                                                   69757
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28545)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28551)
                                                                            (SomeInt 28550)
                                                                            (SomeInt 28549)
                                                                            (SomeInt 28548)
                                                                            (SomeInt 28547)
                                                                            (SomeInt 28546)))))
                                 (a!120 (Build_Document 69753
                                                        69752
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 69751
                                                                    69750
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 69749
                                                                   69748
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 28536)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28542)
                                                                            (SomeInt 28541)
                                                                            (SomeInt 28540)
                                                                            (SomeInt 28539)
                                                                            (SomeInt 28538)
                                                                            (SomeInt 28537)))))
                                 (a!122 (Build_ArrayContentElement
                                          (ContentElementHTML
                                            (Build_HTML 69747
                                                        69746
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 69745
                                                        69744
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 69743
                                                        69742
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 69741
                                                        69740
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 69739
                                                        69738
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 69737
                                                        69736
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))))
                                 (a!144 (= (DOMPath (consInt 0 nilInt)
                                                    (DOMIndex 1))
                                           (DOMPath (consInt 0 nilInt)
                                                    (DOMIndex 1)))))
                           (let ((a!6 (Build_ArrayRequest
                                        (Build_Request MethodGet
                                                       a!1
                                                       a!2
                                                       (SomeInt 35799))
                                        (Build_Request MethodGet
                                                       a!3
                                                       (Build_RequestHeaders
                                                         NoneOrigin
                                                         a!4
                                                         NoneURL)
                                                       (SomeInt 35798))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35797)
                                                                  (url_path_data 76129
                                                                                 76128))
                                                       a!2
                                                       (SomeInt 35796))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35795)
                                                                  (url_path_data 76127
                                                                                 76126))
                                                       a!2
                                                       (SomeInt 35794))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35793)
                                                                  (url_path_data 76125
                                                                                 76124))
                                                       a!2
                                                       (SomeInt 35792))
                                        (Build_Request MethodGet
                                                       a!5
                                                       a!2
                                                       (SomeInt 35791))))
                                 (a!8 (Build_ResponseHeaders
                                        NoneContentType
                                        (SomeSetCookie (Build_SetCookie (NoPrefix 76122)
                                                                        76121
                                                                        NoneDomain
                                                                        (domain 76120)
                                                                        slash
                                                                        false
                                                                        false
                                                                        SSStrict))
                                        (SomeOrigin (OpaqueOrigin 76119))
                                        (SomeURL (Build_URL ProtocolHTTP
                                                            NoneDomain
                                                            (SomeInt 27544)
                                                            (url_path_data 76118
                                                                           76117)))
                                        (SomeCSP (Build_CSP NoneCSPSrc a!7))
                                        NoneReferrerPolicy))
                                 (a!13 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeScript)
                                         a!11
                                         (SomeOrigin (TupleOrigin ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 27465)))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 27543)
                                                             (url_path_data 76112
                                                                            76111)))
                                         a!12
                                         NoneReferrerPolicy))
                                 (a!17 (Build_Response (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35789)
                                                                  (url_path_res (anypath 76110)))
                                                       ResponseNoContent
                                                       a!15
                                                       a!16))
                                 (a!19 (SomeCSP (Build_CSP (SomeCSPSrc (CSPSrcScheme ProtocolHTTP))
                                                           a!18)))
                                 (a!25 (Build_HTML 23969
                                                   23970
                                                   (Build_ArrayoptionHTMLElement
                                                     a!21
                                                     (SomeHTMLElement (HTMLScript a!5))
                                                     a!22
                                                     NoneHTMLElement
                                                     a!23
                                                     a!24)))
                                 (a!29 (Build_CSP a!28
                                                  (SomeTrustedTypes (Build_TrustedTypes
                                                                      (SomeoptionInt NoneInt)
                                                                      true))))
                                 (a!36 (Build_HTML 69721
                                                   69722
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!3))
                                                     a!31
                                                     a!32
                                                     a!33
                                                     a!34
                                                     a!35)))
                                 (a!39 (Build_Response (Build_URL ProtocolHTTP
                                                                  (SomeDomain (domain 76101))
                                                                  (SomeInt 35788)
                                                                  (url_path_data 76100
                                                                                 76099))
                                                       ResponseOk
                                                       a!37
                                                       a!38))
                                 (a!45 (SomeDOMElement (DOMElementResource
                                                         a!5
                                                         (ContentElementScript
                                                           (Build_Script a!5 8)))))
                                 (a!58 (Build_Document 23977
                                                       23978
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 23971
                                                                   23972
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     a!57
                                                                     NoneHTMLElement))
                                                       (Build_DOM 23973
                                                                  23976
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 35780)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 35786)
                                                                           (SomeInt 35785)
                                                                           (SomeInt 35784)
                                                                           (SomeInt 35783)
                                                                           (SomeInt 35782)
                                                                           (SomeInt 35781)))))
                                 (a!68 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!1
                                                                            a!2
                                                                            (SomeInt 35799))
                                                             1)
                                                  nilEvent))
                                 (a!77 (Build_HTML 69721
                                                   69722
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!3))
                                                     a!31
                                                     a!32
                                                     a!76
                                                     a!34
                                                     a!35)))
                                 (a!86 (SomeDOMElement (DOMElementResource
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 27540)
                                                                    (url_path_data 94410
                                                                                   94409))
                                                         a!85)))
                                 (a!106 (SomeDOMElement (DOMElementResource
                                                          (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 28101)
                                                                     (url_path_data 101057
                                                                                    101056))
                                                          a!105)))
                                 (a!113 (Build_ArrayRequest
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28606)
                                                                    (url_path_data 69831
                                                                                   69830))
                                                         a!2
                                                         (SomeInt 28605))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28604)
                                                                    (url_path_data 69829
                                                                                   69828))
                                                         a!2
                                                         (SomeInt 28603))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28602)
                                                                    (url_path_data 69827
                                                                                   69826))
                                                         a!2
                                                         (SomeInt 28601))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28600)
                                                                    (url_path_data 69825
                                                                                   69824))
                                                         a!2
                                                         (SomeInt 28599))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28598)
                                                                    (url_path_data 69823
                                                                                   69822))
                                                         a!2
                                                         (SomeInt 28597))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 28596)
                                                                    (url_path_data 69821
                                                                                   69820))
                                                         a!2
                                                         (SomeInt 28595))))
                                 (a!121 (Build_ArrayWindow
                                          (Build_Window 69801
                                                        (SomeInt 28580)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28588)
                                                                   (url_path_data 69800
                                                                                  69799))
                                                        NoneDomain
                                                        a!115)
                                          (Build_Window 69792
                                                        (SomeInt 28571)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28579)
                                                                   (url_path_data 69791
                                                                                  69790))
                                                        NoneDomain
                                                        a!116)
                                          (Build_Window 69783
                                                        (SomeInt 28562)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28570)
                                                                   (url_path_data 69782
                                                                                  69781))
                                                        NoneDomain
                                                        a!117)
                                          (Build_Window 69774
                                                        (SomeInt 28553)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28561)
                                                                   (url_path_data 69773
                                                                                  69772))
                                                        NoneDomain
                                                        a!118)
                                          (Build_Window 69765
                                                        (SomeInt 28544)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28552)
                                                                   (url_path_data 69764
                                                                                  69763))
                                                        NoneDomain
                                                        a!119)
                                          (Build_Window 69756
                                                        (SomeInt 28535)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 28543)
                                                                   (url_path_data 69755
                                                                                  69754))
                                                        NoneDomain
                                                        a!120))))
                           (let ((a!10 (Build_Response (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35790)
                                                                  (url_path_res (anypath 76123)))
                                                       ResponseNoContent
                                                       a!8
                                                       a!9))
                                 (a!14 (Build_Response a!5
                                                       ResponseOk
                                                       a!13
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!5 8)))))
                                 (a!20 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         NoneSetCookie
                                         (SomeOrigin (OpaqueOrigin 76082))
                                         NoneURL
                                         a!19
                                         NoneReferrerPolicy))
                                 (a!30 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         a!27
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 27668)
                                                             (url_path_data 76080
                                                                            76079)))
                                         (SomeCSP a!29)
                                         NoneReferrerPolicy))
                                 (a!55 (SomeDOMElement (DOMElementResource
                                                         a!3
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 2)
                                                           a!25))))
                                 (a!59 (Build_Window 23979
                                                     (SomeInt 35779)
                                                     (Build_URL ProtocolHTTP
                                                                (SomeDomain (domain 76059))
                                                                (SomeInt 35787)
                                                                (url_path_data 76058
                                                                               76057))
                                                     NoneDomain
                                                     a!58))
                                 (a!65 (SomeDOMElement (DOMElementResource
                                                         a!5
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 0)
                                                           a!25))))
                                 (a!89 (Build_Document 94416
                                                       94415
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 94414
                                                                   94413
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 94412
                                                                  94411
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!86
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!87)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!88)))
                                                       (Build_Initiators (SomeInt 28609)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 28615)
                                                                           (SomeInt 28614)
                                                                           (SomeInt 28613)
                                                                           (SomeInt 28612)
                                                                           (SomeInt 28611)
                                                                           (SomeInt 28610)))))
                                 (a!110 (Build_Document 10794
                                                        10795
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 10790
                                                                    10791
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 10792
                                                                   10793
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     a!106
                                                                     (SomeDOMElement a!107)
                                                                     (SomeDOMElement a!108)
                                                                     (SomeDOMElement a!109)
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 54206)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 54212)
                                                                            (SomeInt 54211)
                                                                            (SomeInt 54210)
                                                                            (SomeInt 54209)
                                                                            (SomeInt 54208)
                                                                            (SomeInt 54207)))))
                                 (a!123 (Build_Global a!113
                                                      a!114
                                                      (Build_ArrayInt 69807
                                                                      69806
                                                                      69805
                                                                      69804
                                                                      69803
                                                                      69802)
                                                      (Build_ArrayEmitter
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient)
                                                      a!121
                                                      a!122
                                                      (Build_ArrayprodOriginoptionCSP
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69735)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69734)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69733)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69732)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69731)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 69730)
                                                          NoneCSP))
                                                      (Build_Config false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false
                                                                    false))))
                           (let ((a!26 (Build_Response a!3
                                                       ResponseOk
                                                       a!20
                                                       (SomeContentElement
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 2)
                                                           a!25))))
                                 (a!49 (Build_Document 9
                                                       2
                                                       a!20
                                                       a!25
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    (SomeDOMElement a!44)
                                                                    a!45
                                                                    (SomeDOMElement a!46)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!47)
                                                                    (SomeDOMElement a!48)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!53 (Build_Document 3
                                                       1
                                                       a!30
                                                       a!36
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!50)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!51)
                                                                    (SomeDOMElement a!52)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!54 (Build_Document 6
                                                       2
                                                       a!20
                                                       a!25
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    (SomeDOMElement a!44)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!46)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!47)
                                                                    (SomeDOMElement a!48)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!56 (Build_Document 6
                                                       1
                                                       a!30
                                                       a!36
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!55
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!50)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!51)
                                                                    (SomeDOMElement a!52)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!66 (Build_Document 9
                                                       1
                                                       a!30
                                                       a!36
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!65
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!50)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!51)
                                                                    (SomeDOMElement a!52)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!67 (EvResponse (Build_Response a!1
                                                                   ResponseOk
                                                                   a!30
                                                                   (SomeContentElement
                                                                     (ContentElementHTML
                                                                       a!36)))
                                                   1))
                                 (a!75 (Build_FetchEngine
                                         8
                                         EmitterClient
                                         (Build_Request MethodGet
                                                        a!5
                                                        a!2
                                                        (SomeInt 35791))
                                         3
                                         (SomeResponse a!14)
                                         a!74))
                                 (a!79 (Build_Document 10
                                                       1
                                                       a!30
                                                       a!77
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!65
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!50)
                                                                    (SomeDOMElement a!78)
                                                                    (SomeDOMElement a!51)
                                                                    (SomeDOMElement a!52)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!90 (Build_Window 94419
                                                     (SomeInt 28608)
                                                     (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 28616)
                                                                (url_path_data 94418
                                                                               94417))
                                                     NoneDomain
                                                     a!89))
                                 (a!111 (Build_Window 105084
                                                      (SomeInt 28070)
                                                      (Build_URL ProtocolHTTP
                                                                 NoneDomain
                                                                 (SomeInt 25712)
                                                                 (url_path_data 96104
                                                                                96103))
                                                      (SomeDomain (domain 100756))
                                                      a!110))
                                 (a!112 (Build_Window 105085
                                                      (SomeInt 28070)
                                                      (Build_URL ProtocolHTTP
                                                                 NoneDomain
                                                                 (SomeInt 25712)
                                                                 (url_path_data 96104
                                                                                96103))
                                                      (SomeDomain (domain 100756))
                                                      a!110))
                                 (a!124 (ite (= (frame_window a!99) 3)
                                             (@3ArrayWindow (windows a!123))
                                             (ite (= (frame_window a!99) 4)
                                                  (@4ArrayWindow (windows a!123))
                                                  (@defaultArrayWindow
                                                    (windows a!123)))))
                                 (a!128 (Build_Window 105083
                                                      (SomeInt 28070)
                                                      (Build_URL ProtocolHTTP
                                                                 NoneDomain
                                                                 (SomeInt 25712)
                                                                 (url_path_data 96104
                                                                                96103))
                                                      (SomeDomain (domain 100756))
                                                      a!110)))
                           (let ((a!40 (Build_ArrayResponse
                                         a!10
                                         a!14
                                         a!17
                                         a!26
                                         (Build_Response a!1
                                                         ResponseOk
                                                         a!30
                                                         (SomeContentElement
                                                           (ContentElementHTML
                                                             a!36)))
                                         a!39))
                                 (a!61 (Build_ArrayWindow
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!3
                                                       NoneDomain
                                                       a!49)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!53)
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!3
                                                       NoneDomain
                                                       a!54)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!56)
                                         a!59
                                         (Build_Window 23986
                                                       (SomeInt 35770)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 35778)
                                                                  (url_path_data 76054
                                                                                 76053))
                                                       NoneDomain
                                                       a!60)))
                                 (a!69 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!3
                                                                            (Build_RequestHeaders
                                                                              NoneOrigin
                                                                              a!4
                                                                              NoneURL)
                                                                            (SomeInt 35798))
                                                             2)
                                                  (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                                   DOMTopLevel))
                                                             (consEvent a!67
                                                                        a!68))))
                                 (a!80 (Build_State 10
                                                    a!75
                                                    (Build_ServiceWorker
                                                      0
                                                      (Build_ArrayoptionInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt
                                                        NoneInt))
                                                    (Build_Window 1
                                                                  NoneInt
                                                                  a!1
                                                                  NoneDomain
                                                                  a!79)
                                                    (Build_ArrayoptionSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      NoneSetCookie
                                                      a!27
                                                      a!11
                                                      NoneSetCookie)
                                                    (Build_ArrayoptionBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob)
                                                    (Build_ArrayoptionStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem
                                                      NoneStorageItem)))
                                 (a!81 (rp_hd_csp (dc_headers (wd_document (Build_Window 1
                                                                                         NoneInt
                                                                                         a!1
                                                                                         NoneDomain
                                                                                         a!66)))))
                                 (a!83 (= (Build_Window 1
                                                        NoneInt
                                                        a!1
                                                        NoneDomain
                                                        a!79)
                                          (Build_Window 1
                                                        NoneInt
                                                        a!1
                                                        NoneDomain
                                                        a!79)))
                                 (a!91 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!92 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!93 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!94 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!95 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!96 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document a!90)))))
                                 (a!125 (ite (= (frame_window a!99) 1)
                                             (@1ArrayWindow (windows a!123))
                                             (ite (= (frame_window a!99) 2)
                                                  (@2ArrayWindow (windows a!123))
                                                  a!124)))
                                 (a!130 (dm_body (dc_dom (wd_document (Build_Window 1
                                                                                    NoneInt
                                                                                    a!1
                                                                                    NoneDomain
                                                                                    a!79)))))
                                 (a!138 (= (Build_Window 2
                                                         (SomeInt 3)
                                                         a!3
                                                         NoneDomain
                                                         a!49)
                                           (Build_Window 2
                                                         (SomeInt 3)
                                                         a!3
                                                         NoneDomain
                                                         a!49)))
                                 (a!147 (dc_dom (wd_document (Build_Window 2
                                                                           (SomeInt 3)
                                                                           a!3
                                                                           NoneDomain
                                                                           a!49))))
                                 (a!152 ((_ is ProtocolHTTPS)
                                          (url_protocol (wd_location (Build_Window 1
                                                                                   NoneInt
                                                                                   a!1
                                                                                   NoneDomain
                                                                                   a!66))))))
                           (let ((a!64 (Build_Global a!6
                                                     a!40
                                                     (Build_ArrayInt 4
                                                                     3
                                                                     23966
                                                                     23967
                                                                     23968
                                                                     1)
                                                     (Build_ArrayEmitter
                                                       a!41
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       a!42
                                                       a!43)
                                                     a!61
                                                     a!62
                                                     (Build_ArrayprodOriginoptionCSP
                                                       a!63
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 76040)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 76039)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 76038)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 76037)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 76036)
                                                         NoneCSP))
                                                     (Build_Config false
                                                                   true
                                                                   false
                                                                   false
                                                                   true
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false)))
                                 (a!70 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                        (DOMIndex 0)))
                                                  (consEvent (EvResponse a!26 2)
                                                             a!69)))
                                 (a!82 (tt_policy (@0SomeTrustedTypes
                                                    (csp_trusted_types
                                                      (@0SomeCSP a!81)))))
                                 (a!97 (ite (= 0 2)
                                            a!93
                                            (ite (= 0 3)
                                                 a!94
                                                 (ite (= 0 4) a!95 a!96))))
                                 (a!126 (= (ite (= (frame_window a!99) 0)
                                                (@0ArrayWindow (windows a!123))
                                                a!125)
                                           a!111))
                                 (a!131 (ite (= 0 2)
                                             (@2ArrayoptionDOMElement a!130)
                                             (ite (= 0 3)
                                                  (@3ArrayoptionDOMElement
                                                    a!130)
                                                  (ite (= 0 4)
                                                       (@4ArrayoptionDOMElement
                                                         a!130)
                                                       (@defaultArrayoptionDOMElement
                                                         a!130)))))
                                 (a!146 (tt_require_for_script
                                          (@0SomeTrustedTypes
                                            (csp_trusted_types (@0SomeCSP a!81)))))
                                 (a!148 (ite (= 1 3)
                                             (@3ArrayoptionDOMElement
                                               (dm_body a!147))
                                             (ite (= 1 4)
                                                  (@4ArrayoptionDOMElement
                                                    (dm_body a!147))
                                                  (@defaultArrayoptionDOMElement
                                                    (dm_body a!147))))))
                           (let ((a!71 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!5
                                                                            a!2
                                                                            (SomeInt 35791))
                                                             3)
                                                  a!70))
                                 (a!84 (and a!83
                                            a!83
                                            (= (st_window a!80)
                                               (Build_Window 1
                                                             NoneInt
                                                             a!1
                                                             NoneDomain
                                                             a!79))
                                            (= (DOMPath nilInt (DOMIndex 3))
                                               (DOMPath nilInt (DOMIndex 3)))
                                            (= (DOMPath nilInt (DOMIndex 3))
                                               (DOMPath nilInt (DOMIndex 3)))
                                            (= a!64 a!64)))
                                 (a!98 (ite (= 0 0)
                                            a!91
                                            (ite (= 0 1) a!92 a!97)))
                                 (a!129 (and (= (Build_Window 2
                                                              (SomeInt 3)
                                                              a!3
                                                              NoneDomain
                                                              a!49)
                                                a!128)
                                             (= a!128 E)
                                             (= (st_window a!80) E)
                                             (= B (DOMPath nilInt DOMTopLevel))
                                             (= (DOMPath (consInt 0 nilInt)
                                                         (DOMIndex 1))
                                                B)
                                             (= a!64 A)))
                                 (a!132 (ite (= 0 0)
                                             (@0ArrayoptionDOMElement a!130)
                                             (ite (= 0 1)
                                                  (@1ArrayoptionDOMElement
                                                    a!130)
                                                  a!131)))
                                 (a!139 (ite (= (frame_window (Build_Frame a!3
                                                                           0))
                                                4)
                                             (@4ArrayWindow (windows a!64))
                                             (@defaultArrayWindow
                                               (windows a!64))))
                                 (a!149 (ite (= 1 1)
                                             (@1ArrayoptionDOMElement
                                               (dm_body a!147))
                                             (ite (= 1 2)
                                                  (@2ArrayoptionDOMElement
                                                    (dm_body a!147))
                                                  a!148))))
                           (let ((a!72 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                                 nilInt)
                                                                        (DOMIndex 1)))
                                                  (consEvent (EvResponse a!14 3)
                                                             a!71)))
                                 (a!100 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!98)))
                                           a!99))
                                 (a!101 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!98)))
                                           L))
                                 (a!102 (not ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!98)))))
                                 (a!103 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!98)))))
                                 (a!104 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!98)))))
                                 (a!133 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!132)))
                                           (Build_Frame a!3 0)))
                                 (a!134 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!132)))
                                           a!25))
                                 (a!135 (not ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!132)))))
                                 (a!136 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!132)))))
                                 (a!137 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!132)))))
                                 (a!140 (ite (= (frame_window (Build_Frame a!3
                                                                           0))
                                                3)
                                             (@3ArrayWindow (windows a!64))
                                             a!139))
                                 (a!150 (@0SomeDOMElement (ite (= 1 0)
                                                               (@0ArrayoptionDOMElement
                                                                 (dm_body a!147))
                                                               a!149)))
                                 (a!151 ((_ is SomeDOMElement)
                                          (ite (= 1 0)
                                               (@0ArrayoptionDOMElement
                                                 (dm_body a!147))
                                               a!149))))
                           (let ((a!73 (consEvent (EvScriptUpdateHTML
                                                    (DOMPath (consInt 0 nilInt)
                                                             (DOMIndex 1))
                                                    (DOMPath nilInt
                                                             (DOMIndex 3))
                                                    (Build_Window 1
                                                                  NoneInt
                                                                  a!1
                                                                  NoneDomain
                                                                  a!66))
                                                  a!72))
                                 (a!127 (and a!100
                                             a!101
                                             a!102
                                             a!103
                                             a!104
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!98)))
                                             ((_ is SomeDOMElement) a!98)
                                             (= (Build_Window 1
                                                              NoneInt
                                                              a!1
                                                              NoneDomain
                                                              a!79)
                                                Q)
                                             (= Q V)
                                             (= a!111 a!112)
                                             (= V a!112)
                                             a!126
                                             (= (st_window a!80) a!90)
                                             (= (DOMPath nilInt (DOMIndex 3)) I)
                                             (= T (DOMPath nilInt DOMTopLevel))
                                             (= T (DOMPath nilInt DOMTopLevel))
                                             (= I
                                                (DOMPath (consInt 0 nilInt)
                                                         DOMTopLevel))
                                             (= a!64 a!123)
                                             (= a!123 S)))
                                 (a!141 (ite (= (frame_window (Build_Frame a!3
                                                                           0))
                                                2)
                                             (@2ArrayWindow (windows a!64))
                                             a!140)))
                           (let ((a!142 (ite (= (frame_window (Build_Frame a!3
                                                                           0))
                                                1)
                                             (@1ArrayWindow (windows a!64))
                                             a!141)))
                           (let ((a!143 (ite (= (frame_window (Build_Frame a!3
                                                                           0))
                                                0)
                                             (@0ArrayWindow (windows a!64))
                                             a!142)))
                           (let ((a!145 (and a!133
                                             a!134
                                             a!135
                                             a!136
                                             a!137
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!132)))
                                             ((_ is SomeDOMElement) a!132)
                                             a!138
                                             a!138
                                             a!138
                                             a!138
                                             (= a!143
                                                (Build_Window 2
                                                              (SomeInt 3)
                                                              a!3
                                                              NoneDomain
                                                              a!49))
                                             (= (st_window a!80)
                                                (Build_Window 1
                                                              NoneInt
                                                              a!1
                                                              NoneDomain
                                                              a!79))
                                             (= (DOMPath nilInt (DOMIndex 1))
                                                (DOMPath nilInt (DOMIndex 1)))
                                             (= (DOMPath nilInt (DOMIndex 1))
                                                (DOMPath nilInt (DOMIndex 1)))
                                             a!144
                                             a!144
                                             (= a!64 a!64)
                                             (= a!64 a!64))))
                           (let ((a!153 (and (Reachable a!64 a!73 a!80)
                                             ((_ is NoneInt)
                                               (@0SomeoptionInt a!82))
                                             (or a!84 a!127)
                                             (or a!129 a!145)
                                             a!146
                                             (c_restrict_tt_to_secure_contexts
                                               (config a!64))
                                             (not (c_tt_strict_realm_check
                                                    (config a!64)))
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource a!150))
                                             (not ((_ is ContentElementImage)
                                                    (@1DOMElementResource a!150)))
                                             (not ((_ is ContentElementHTML)
                                                    (@1DOMElementResource a!150)))
                                             (not ((_ is DOMElementForm) a!150))
                                             a!151
                                             a!152
                                             ((_ is SomeoptionInt) a!82)
                                             ((_ is SomeCSP) a!81)
                                             (= a!73 a!73)
                                             (= a!73 a!73)
                                             ((_ is Build_CSP) (@0SomeCSP a!81))
                                             ((_ is SomeTrustedTypes)
                                               (csp_trusted_types
                                                 (@0SomeCSP a!81))))))
                             (=> a!153 (query!0 a!80 a!73 a!64)))))))))))))))
                           :weight 0))))
      (a!9 (Build_ArrayRequest
             (Build_Request MethodGet a!4 a!5 (SomeInt 35799))
             (Build_Request MethodGet
                            a!6
                            (Build_RequestHeaders NoneOrigin a!7 NoneURL)
                            (SomeInt 35798))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35797)
                                       (url_path_data 76129 76128))
                            a!5
                            (SomeInt 35796))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35795)
                                       (url_path_data 76127 76126))
                            a!5
                            (SomeInt 35794))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35793)
                                       (url_path_data 76125 76124))
                            a!5
                            (SomeInt 35792))
             (Build_Request MethodGet a!8 a!5 (SomeInt 35791))))
      (a!11 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 76122)
                                              76121
                                              NoneDomain
                                              (domain 76120)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 76119))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 27544)
                                  (url_path_data 76118 76117)))
              (SomeCSP (Build_CSP NoneCSPSrc a!10))
              NoneReferrerPolicy))
      (a!16 (Build_ResponseHeaders
              (SomeContentType ContentTypeScript)
              a!14
              (SomeOrigin (TupleOrigin ProtocolHTTP NoneDomain (SomeInt 27465)))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 27543)
                                  (url_path_data 76112 76111)))
              a!15
              NoneReferrerPolicy))
      (a!20 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35789)
                                       (url_path_res (anypath 76110)))
                            ResponseNoContent
                            a!18
                            a!19))
      (a!22 (SomeCSP (Build_CSP (SomeCSPSrc (CSPSrcScheme ProtocolHTTP)) a!21)))
      (a!28 (Build_HTML 23969
                        23970
                        (Build_ArrayoptionHTMLElement
                          a!24
                          (SomeHTMLElement (HTMLScript a!8))
                          a!25
                          NoneHTMLElement
                          a!26
                          a!27)))
      (a!32 (Build_CSP a!31
                       (SomeTrustedTypes (Build_TrustedTypes
                                           (SomeoptionInt NoneInt)
                                           true))))
      (a!39 (Build_HTML 69721
                        69722
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!6))
                          a!34
                          a!35
                          a!36
                          a!37
                          a!38)))
      (a!42 (Build_Response (Build_URL ProtocolHTTP
                                       (SomeDomain (domain 76101))
                                       (SomeInt 35788)
                                       (url_path_data 76100 76099))
                            ResponseOk
                            a!40
                            a!41))
      (a!48 (SomeDOMElement (DOMElementResource
                              a!8
                              (ContentElementScript (Build_Script a!8 8)))))
      (a!61 (Build_Document 23977
                            23978
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 23971
                                        23972
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          a!60
                                          NoneHTMLElement))
                            (Build_DOM 23973
                                       23976
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 35780)
                                              (Build_ArrayoptionInt
                                                (SomeInt 35786)
                                                (SomeInt 35785)
                                                (SomeInt 35784)
                                                (SomeInt 35783)
                                                (SomeInt 35782)
                                                (SomeInt 35781)))))
      (a!69 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!4
                                                 a!5
                                                 (SomeInt 35799))
                                  1)
                       nilEvent))
      (a!80 (Build_HTML 69721
                        69722
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!6))
                          a!34
                          a!35
                          a!79
                          a!37
                          a!38)))
      (a!105 (Build_State 1
                          (Build_FetchEngine
                            1
                            EmitterClient
                            (Build_Request MethodGet a!4 a!5 (SomeInt 35799))
                            1
                            NoneResponse
                            (Build_ArrayoptionprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt))
                          (Build_ServiceWorker
                            0
                            (Build_ArrayoptionInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt))
                          a!102
                          (Build_ArrayoptionSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie)
                          (Build_ArrayoptionBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob)
                          (Build_ArrayoptionStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem)))
      (a!106 (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       (SomeDomain (domain 0))
                                       (SomeInt 0)
                                       (url_path_res slash))
                            a!5
                            NoneInt)))
(let ((a!13 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35790)
                                       (url_path_res (anypath 76123)))
                            ResponseNoContent
                            a!11
                            a!12))
      (a!17 (Build_Response a!8
                            ResponseOk
                            a!16
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!8 8)))))
      (a!23 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 76082))
              NoneURL
              a!22
              NoneReferrerPolicy))
      (a!33 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              a!30
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 27668)
                                  (url_path_data 76080 76079)))
              (SomeCSP a!32)
              NoneReferrerPolicy))
      (a!58 (SomeDOMElement (DOMElementResource
                              a!6
                              (ContentElementFrame (Build_Frame a!6 2) a!28))))
      (a!62 (Build_Window 23979
                          (SomeInt 35779)
                          (Build_URL ProtocolHTTP
                                     (SomeDomain (domain 76059))
                                     (SomeInt 35787)
                                     (url_path_data 76058 76057))
                          NoneDomain
                          a!61))
      (a!76 (SomeDOMElement (DOMElementResource
                              a!8
                              (ContentElementFrame (Build_Frame a!6 0) a!28))))
      (a!107 (Build_State 0
                          (Build_FetchEngine
                            0
                            EmitterClient
                            a!106
                            0
                            NoneResponse
                            (Build_ArrayoptionprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt
                              NoneprodprodEmitterIntInt))
                          (Build_ServiceWorker
                            0
                            (Build_ArrayoptionInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt))
                          a!102
                          (Build_ArrayoptionSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie)
                          (Build_ArrayoptionBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob
                            NoneBlob)
                          (Build_ArrayoptionStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem))))
(let ((a!29 (Build_Response a!6
                            ResponseOk
                            a!23
                            (SomeContentElement
                              (ContentElementFrame (Build_Frame a!6 2) a!28))))
      (a!52 (Build_Document 9
                            2
                            a!23
                            a!28
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!47)
                                         a!48
                                         (SomeDOMElement a!49)
                                         NoneDOMElement
                                         (SomeDOMElement a!50)
                                         (SomeDOMElement a!51)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!56 (Build_Document 3
                            1
                            a!33
                            a!39
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!53)
                                         NoneDOMElement
                                         (SomeDOMElement a!54)
                                         (SomeDOMElement a!55)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!57 (Build_Document 6
                            2
                            a!23
                            a!28
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!47)
                                         NoneDOMElement
                                         (SomeDOMElement a!49)
                                         NoneDOMElement
                                         (SomeDOMElement a!50)
                                         (SomeDOMElement a!51)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!59 (Build_Document 6
                            1
                            a!33
                            a!39
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!58
                                         NoneDOMElement
                                         (SomeDOMElement a!53)
                                         NoneDOMElement
                                         (SomeDOMElement a!54)
                                         (SomeDOMElement a!55)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!68 (EvResponse (Build_Response a!4
                                        ResponseOk
                                        a!33
                                        (SomeContentElement
                                          (ContentElementHTML a!39)))
                        1))
      (a!75 (Build_FetchEngine
              8
              EmitterClient
              (Build_Request MethodGet a!8 a!5 (SomeInt 35791))
              3
              (SomeResponse a!17)
              a!74))
      (a!77 (Build_Document 9
                            1
                            a!33
                            a!39
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!76
                                         NoneDOMElement
                                         (SomeDOMElement a!53)
                                         NoneDOMElement
                                         (SomeDOMElement a!54)
                                         (SomeDOMElement a!55)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!82 (Build_Document 10
                            1
                            a!33
                            a!80
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!76
                                         NoneDOMElement
                                         (SomeDOMElement a!53)
                                         (SomeDOMElement a!81)
                                         (SomeDOMElement a!54)
                                         (SomeDOMElement a!55)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!99 (SomeResponse (Build_Response a!4
                                          ResponseOk
                                          a!33
                                          (SomeContentElement
                                            (ContentElementHTML a!39))))))
(let ((a!43 (Build_ArrayResponse
              a!13
              a!17
              a!20
              a!29
              (Build_Response a!4
                              ResponseOk
                              a!33
                              (SomeContentElement (ContentElementHTML a!39)))
              a!42))
      (a!64 (Build_ArrayWindow
              (Build_Window 2 (SomeInt 3) a!6 NoneDomain a!52)
              (Build_Window 1 NoneInt a!4 NoneDomain a!56)
              (Build_Window 2 (SomeInt 3) a!6 NoneDomain a!57)
              (Build_Window 1 NoneInt a!4 NoneDomain a!59)
              a!62
              (Build_Window 23986
                            (SomeInt 35770)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 35778)
                                       (url_path_data 76054 76053))
                            NoneDomain
                            a!63)))
      (a!70 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!6
                                                 (Build_RequestHeaders
                                                   NoneOrigin
                                                   a!7
                                                   NoneURL)
                                                 (SomeInt 35798))
                                  2)
                       (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                  (consEvent a!68 a!69))))
      (a!83 (Build_State 10
                         a!75
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!4 NoneDomain a!82)
                         (Build_ArrayoptionSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           a!30
                           a!14
                           NoneSetCookie)
                         (Build_ArrayoptionBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob)
                         (Build_ArrayoptionStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem)))
      (a!90 (Build_State 7
                         (Build_FetchEngine
                           7
                           EmitterClient
                           (Build_Request MethodGet a!8 a!5 (SomeInt 35791))
                           3
                           NoneResponse
                           a!89)
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!4 NoneDomain a!59)
                         (Build_ArrayoptionSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           a!30
                           NoneSetCookie
                           NoneSetCookie)
                         (Build_ArrayoptionBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob)
                         (Build_ArrayoptionStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem)))
      (a!92 (Build_FetchEngine
              5
              EmitterClient
              (Build_Request MethodGet
                             a!6
                             (Build_RequestHeaders NoneOrigin a!7 NoneURL)
                             (SomeInt 35798))
              2
              (SomeResponse a!29)
              a!89))
      (a!97 (Build_State 4
                         (Build_FetchEngine
                           4
                           EmitterClient
                           (Build_Request MethodGet
                                          a!6
                                          (Build_RequestHeaders
                                            NoneOrigin
                                            a!7
                                            NoneURL)
                                          (SomeInt 35798))
                           2
                           NoneResponse
                           a!96)
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!4 NoneDomain a!56)
                         (Build_ArrayoptionSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           NoneSetCookie
                           a!30
                           NoneSetCookie
                           NoneSetCookie)
                         (Build_ArrayoptionBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob
                           NoneBlob)
                         (Build_ArrayoptionStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem
                           NoneStorageItem)))
      (a!100 (Build_FetchEngine
               2
               EmitterClient
               (Build_Request MethodGet a!4 a!5 (SomeInt 35799))
               1
               a!99
               a!96)))
(let ((a!67 (Build_Global a!9
                          a!43
                          (Build_ArrayInt 4 3 23966 23967 23968 1)
                          (Build_ArrayEmitter
                            a!44
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            a!45
                            a!46)
                          a!64
                          a!65
                          (Build_ArrayprodOriginoptionCSP
                            a!66
                            (pairOriginoptionCSP (OpaqueOrigin 76040) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 76039) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 76038) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 76037) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 76036) NoneCSP))
                          (Build_Config false
                                        true
                                        false
                                        false
                                        true
                                        false
                                        false
                                        false
                                        false
                                        false
                                        false
                                        false)))
      (a!71 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 0)))
                       (consEvent (EvResponse a!29 2) a!70))))
(let ((a!72 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!8
                                                 a!5
                                                 (SomeInt 35791))
                                  3)
                       a!71))
      (a!93 (Reachable a!67
                       a!71
                       (Build_State 6
                                    a!92
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!4 NoneDomain a!59)
                                    (Build_ArrayoptionSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      a!30
                                      NoneSetCookie
                                      NoneSetCookie)
                                    (Build_ArrayoptionBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob)
                                    (Build_ArrayoptionStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem))))
      (a!95 (Reachable a!67
                       (consEvent (EvResponse a!29 2) a!70)
                       (Build_State 5
                                    a!92
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!4 NoneDomain a!56)
                                    (Build_ArrayoptionSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      a!30
                                      NoneSetCookie
                                      NoneSetCookie)
                                    (Build_ArrayoptionBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob)
                                    (Build_ArrayoptionStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem))))
      (a!101 (Reachable a!67
                        (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                   (consEvent a!68 a!69))
                        (Build_State 3
                                     a!100
                                     (Build_ServiceWorker
                                       0
                                       (Build_ArrayoptionInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt))
                                     (Build_Window 1
                                                   NoneInt
                                                   a!4
                                                   NoneDomain
                                                   a!56)
                                     (Build_ArrayoptionSetCookie
                                       NoneSetCookie
                                       NoneSetCookie
                                       NoneSetCookie
                                       a!30
                                       NoneSetCookie
                                       NoneSetCookie)
                                     (Build_ArrayoptionBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob)
                                     (Build_ArrayoptionStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem))))
      (a!103 (Reachable a!67
                        (consEvent a!68 a!69)
                        (Build_State 2
                                     a!100
                                     (Build_ServiceWorker
                                       0
                                       (Build_ArrayoptionInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt))
                                     a!102
                                     (Build_ArrayoptionSetCookie
                                       NoneSetCookie
                                       NoneSetCookie
                                       NoneSetCookie
                                       a!30
                                       NoneSetCookie
                                       NoneSetCookie)
                                     (Build_ArrayoptionBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob
                                       NoneBlob)
                                     (Build_ArrayoptionStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem
                                       NoneStorageItem)))))
(let ((a!73 (consEvent (EvDOMUpdate (DOMPath (consInt 0 nilInt) (DOMIndex 1)))
                       (consEvent (EvResponse a!17 3) a!72)))
      (a!86 (Reachable a!67
                       (consEvent (EvResponse a!17 3) a!72)
                       (Build_State 8
                                    a!75
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!4 NoneDomain a!59)
                                    (Build_ArrayoptionSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      a!30
                                      a!14
                                      NoneSetCookie)
                                    (Build_ArrayoptionBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob)
                                    (Build_ArrayoptionStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem)))))
(let ((a!78 (Reachable a!67
                       a!73
                       (Build_State 9
                                    a!75
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!4 NoneDomain a!77)
                                    (Build_ArrayoptionSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      NoneSetCookie
                                      a!30
                                      a!14
                                      NoneSetCookie)
                                    (Build_ArrayoptionBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob
                                      NoneBlob)
                                    (Build_ArrayoptionStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem
                                      NoneStorageItem))))
      (a!84 (consEvent (EvScriptUpdateHTML
                         (DOMPath (consInt 0 nilInt) (DOMIndex 1))
                         (DOMPath nilInt (DOMIndex 3))
                         (Build_Window 1 NoneInt a!4 NoneDomain a!77))
                       a!73)))
(let ((a!87 (hyper-res (hyper-res a!2 a!3 (=> a!78 (query!0 a!83 a!84 a!67)))
                       a!85
                       (=> a!86 (query!0 a!83 a!84 a!67)))))
(let ((a!94 (hyper-res (hyper-res a!87
                                  a!88
                                  (=> (Reachable a!67 a!72 a!90)
                                      (query!0 a!83 a!84 a!67)))
                       a!91
                       (=> a!93 (query!0 a!83 a!84 a!67)))))
(let ((a!98 (hyper-res (hyper-res a!94 a!85 (=> a!95 (query!0 a!83 a!84 a!67)))
                       a!88
                       (=> (Reachable a!67 a!70 a!97) (query!0 a!83 a!84 a!67)))))
(let ((a!104 (hyper-res (hyper-res a!98
                                   a!91
                                   (=> a!101 (query!0 a!83 a!84 a!67)))
                        a!85
                        (=> a!103 (query!0 a!83 a!84 a!67)))))
(let ((a!108 (hyper-res (hyper-res a!104
                                   a!88
                                   (=> (Reachable a!67 a!69 a!105)
                                       (query!0 a!83 a!84 a!67)))
                        a!91
                        (=> (Reachable a!67 nilEvent a!107)
                            (query!0 a!83 a!84 a!67)))))
  (hyper-res a!108 a!109 (query!0 a!83 a!84 a!67))))))))))))))))
