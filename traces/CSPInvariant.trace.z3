
(let ((a!1 (asserted (forall ((A NestedDOMPath)
                              (B Int)
                              (C Window)
                              (D HTML)
                              (E Frame)
                              (F listInt)
                              (G DOMSelector)
                              (H Window)
                              (I Window)
                              (J Global)
                              (K Global)
                              (L NestedDOMPath)
                              (M DOMSelector)
                              (N Window)
                              (O Window)
                              (P Global)
                              (Q Global)
                              (R NestedDOMPath)
                              (S DOMSelector)
                              (T Window)
                              (U Window)
                              (V listInt)
                              (W Int)
                              (X Window)
                              (Y DOMSelector)
                              (Z Window)
                              (A1 listEvent)
                              (B1 listEvent)
                              (C1 State))
                       (! (let ((a!1 (rp_hd_csp (dc_headers (wd_document (st_window C1)))))
                                (a!2 (@0ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!3 (@1ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!4 (@2ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!5 (@3ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!6 (@4ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!7 (@defaultArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document X)))))
                                (a!10 (consEvent (EvScriptUpdateHTML
                                                   (DOMPath V (DOMIndex W))
                                                   (DOMPath nilInt Y)
                                                   Z)
                                                 A1))
                                (a!11 ((_ is ProtocolHTTPS)
                                        (url_protocol (wd_location (st_window C1)))))
                                (a!12 ((_ is ProtocolHTTP)
                                        (url_protocol (wd_location (st_window C1)))))
                                (a!13 (TupleOrigin (url_protocol (wd_location (st_window C1)))
                                                   (url_host (wd_location (st_window C1)))
                                                   (url_port (wd_location (st_window C1)))))
                                (a!14 ((_ is ProtocolData)
                                        (url_protocol (wd_location (st_window C1)))))
                                (a!15 ((_ is url_path_data)
                                        (url_path (wd_location (st_window C1)))))
                                (a!16 (@0url_path_data (url_path (wd_location (st_window C1)))))
                                (a!17 ((_ is url_path_blob)
                                        (url_path (wd_location (st_window C1)))))
                                (a!18 (@0url_path_blob (url_path (wd_location (st_window C1)))))
                                (a!57 (and (= T U)
                                           (= X T)
                                           (= (st_window C1) U)
                                           (= R (DOMPath nilInt S))
                                           (= (DOMPath V (DOMIndex W)) R)
                                           (= P Q)))
                                (a!58 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!59 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!60 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!61 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!62 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!63 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!70 (ite (= (frame_window E) 3)
                                           (@3ArrayWindow (windows J))
                                           (ite (= (frame_window E) 4)
                                                (@4ArrayWindow (windows J))
                                                (@defaultArrayWindow
                                                  (windows J))))))
                          (let ((a!8 (ite (= W 2)
                                          a!4
                                          (ite (= W 3)
                                               a!5
                                               (ite (= W 4) a!6 a!7))))
                                (a!19 (ite a!14
                                           (ite a!15
                                                (SomeOrigin (OpaqueOrigin a!16))
                                                NoneOrigin)
                                           (ite a!15
                                                NoneOrigin
                                                (ite a!17
                                                     (SomeOrigin a!18)
                                                     NoneOrigin))))
                                (a!20 (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!21 (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!22 (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!23 (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!24 (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!48 (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))))
                                (a!51 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))
                                         CSPSrcSelf))
                                (a!64 (ite (= B 2)
                                           a!60
                                           (ite (= B 3)
                                                a!61
                                                (ite (= B 4) a!62 a!63))))
                                (a!71 (ite (= (frame_window E) 1)
                                           (@1ArrayWindow (windows J))
                                           (ite (= (frame_window E) 2)
                                                (@2ArrayWindow (windows J))
                                                a!70))))
                          (let ((a!9 (ite (= W 0) a!2 (ite (= W 1) a!3 a!8)))
                                (a!25 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))
                                         (CSPSrcSource a!20 a!21 a!22 a!23 a!24)))
                                (a!34 (not (= a!23 (SomeInt (@0SomeInt a!23)))))
                                (a!36 (not (= a!20
                                              (SomeProtocol (@0SomeProtocol a!20)))))
                                (a!38 (not (= a!24 (SomePath (@0SomePath a!24)))))
                                (a!41 (not (= a!21
                                              (SomeoptionInt (@0SomeoptionInt a!21)))))
                                (a!43 (= (@0SomeoptionInt a!21)
                                         (SomeInt (@0SomeInt (@0SomeoptionInt a!21)))))
                                (a!49 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!1)))
                                         (CSPSrcScheme a!48)))
                                (a!52 (SomeOrigin (@0SomeOrigin (ite (or a!11
                                                                         a!12)
                                                                     (SomeOrigin a!13)
                                                                     a!19))))
                                (a!65 (ite (= B 0) a!58 (ite (= B 1) a!59 a!64)))
                                (a!72 (= (ite (= (frame_window E) 0)
                                              (@0ArrayWindow (windows J))
                                              a!71)
                                         H)))
                          (let ((a!26 (script_src (@0ContentElementScript
                                                    (@1DOMElementResource
                                                      (@0SomeDOMElement a!9)))))
                                (a!66 (= (@0SomeDOMElement a!65)
                                         (DOMElementResource
                                           (@0DOMElementResource
                                             (@0SomeDOMElement a!65))
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!65)))))
                                (a!67 (ContentElementFrame
                                        (@0ContentElementFrame
                                          (@1DOMElementResource
                                            (@0SomeDOMElement a!65)))
                                        (@1ContentElementFrame
                                          (@1DOMElementResource
                                            (@0SomeDOMElement a!65)))))
                                (a!68 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!65)))
                                         E))
                                (a!69 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!65)))
                                         D)))
                          (let ((a!27 (= (url_host a!26)
                                         (SomeDomain (@0SomeDomain (url_host a!26)))))
                                (a!28 (= (@0domain (@0SomeDomain (url_host a!26)))
                                         a!22))
                                (a!29 (domain (@0domain (@0SomeDomain (url_host a!26)))))
                                (a!31 (= (@1subdomain (@0SomeDomain (url_host a!26)))
                                         a!22))
                                (a!32 (subdomain (@0subdomain (@0SomeDomain (url_host a!26)))
                                                 (@1subdomain (@0SomeDomain (url_host a!26)))))
                                (a!35 (not (= (url_port a!26)
                                              (SomeInt (@0SomeInt a!23)))))
                                (a!37 (or a!36
                                          (not (= (url_protocol a!26)
                                                  (@0SomeProtocol a!20)))))
                                (a!39 (= (url_path a!26)
                                         (url_path_res (@0url_path_res (url_path a!26)))))
                                (a!40 (not (= (@0url_path_res (url_path a!26))
                                              (@0SomePath a!24))))
                                (a!44 (= (@0subdomain (@0SomeDomain (url_host a!26)))
                                         (@0SomeInt (@0SomeoptionInt a!21))))
                                (a!50 (or (not a!49)
                                          (not (= (url_protocol a!26) a!48))))
                                (a!53 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!26)))))
                                (a!54 (ite ((_ is url_path_blob)
                                             (url_path a!26))
                                           (SomeOrigin (@0url_path_blob (url_path a!26)))
                                           NoneOrigin))
                                (a!73 (and (= a!65
                                              (SomeDOMElement (@0SomeDOMElement a!65)))
                                           a!66
                                           (= (@1DOMElementResource
                                                (@0SomeDOMElement a!65))
                                              a!67)
                                           a!68
                                           a!69
                                           (= N O)
                                           (= I N)
                                           (= H O)
                                           (= X I)
                                           (= (st_window C1) C)
                                           a!72
                                           (= A (DOMPath (consInt B F) G))
                                           (= L (DOMPath F G))
                                           (= L (DOMPath nilInt M))
                                           (= (DOMPath V (DOMIndex W)) A)
                                           (= J K)
                                           (= P J))))
                          (let ((a!30 (not (= (@0SomeDomain (url_host a!26))
                                              a!29)))
                                (a!33 (not (= (@0SomeDomain (url_host a!26))
                                              a!32)))
                                (a!55 (ite ((_ is ProtocolData)
                                             (url_protocol a!26))
                                           (ite ((_ is url_path_data)
                                                  (url_path a!26))
                                                a!53
                                                NoneOrigin)
                                           (ite ((_ is url_path_data)
                                                  (url_path a!26))
                                                NoneOrigin
                                                a!54))))
                          (let ((a!42 (or (not (= (@0SomeoptionInt a!21)
                                                  NoneInt))
                                          (not a!27)
                                          a!33))
                                (a!56 (ite (or ((_ is ProtocolHTTPS)
                                                 (url_protocol a!26))
                                               ((_ is ProtocolHTTP)
                                                 (url_protocol a!26)))
                                           (SomeOrigin (TupleOrigin (url_protocol a!26)
                                                                    (url_host a!26)
                                                                    (url_port a!26)))
                                           a!55)))
                          (let ((a!45 (or a!41
                                          (and a!42
                                               (or (not a!43)
                                                   (not a!27)
                                                   a!33
                                                   (not a!44))))))
                          (let ((a!46 (and a!45
                                           (or (not (= a!21 NoneoptionInt))
                                               (not a!27)
                                               a!30))))
                          (let ((a!47 (or (not a!25)
                                          (not a!27)
                                          (and (or (not a!28) a!30)
                                               (or (not a!31) a!33))
                                          (and (or a!34 a!35)
                                               (not (= a!23 NoneInt)))
                                          (and a!37 (not (= a!20 NoneProtocol)))
                                          (and (or a!38 (not a!39) a!40)
                                               (not (= a!24 NonePath)))
                                          a!46)))
                          (let ((a!74 (and (Reachable P B1 C1)
                                           ((_ is Build_CSP) (@0SomeCSP a!1))
                                           ((_ is SomeCSP) a!1)
                                           ((_ is DOMElementResource)
                                             (@0SomeDOMElement a!9))
                                           ((_ is SomeDOMElement) a!9)
                                           (= B1 a!10)
                                           ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!9)))
                                           ((_ is SomeOrigin)
                                             (ite (or a!11 a!12)
                                                  (SomeOrigin a!13)
                                                  a!19))
                                           a!47
                                           a!50
                                           (or (not a!51) (not (= a!52 a!56)))
                                           (or a!57 a!73)
                                           ((_ is SomeCSPSrc)
                                             (csp_script_src (@0SomeCSP a!1))))))
                            (=> a!74 (query!0 C1 B1 P)))))))))))))
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
                                (a!13 (= (wd_document_domain V7)
                                         (SomeDomain (@0SomeDomain (wd_document_domain
                                                                     V7)))))
                                (a!14 (= (wd_document_domain Q7)
                                         (SomeDomain (@0SomeDomain (wd_document_domain
                                                                     Q7)))))
                                (a!16 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location V7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location V7)))))
                                (a!17 (SomeOrigin (TupleOrigin (url_protocol (wd_location V7))
                                                               (url_host (wd_location V7))
                                                               (url_port (wd_location V7)))))
                                (a!18 (OpaqueOrigin (@0url_path_data (url_path (wd_location V7)))))
                                (a!20 (SomeOrigin (@0url_path_blob (url_path (wd_location V7)))))
                                (a!24 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location Q7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location Q7)))))
                                (a!25 (SomeOrigin (TupleOrigin (url_protocol (wd_location Q7))
                                                               (url_host (wd_location Q7))
                                                               (url_port (wd_location Q7)))))
                                (a!26 (OpaqueOrigin (@0url_path_data (url_path (wd_location Q7)))))
                                (a!28 (SomeOrigin (@0url_path_blob (url_path (wd_location Q7)))))
                                (a!33 (@1ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!34 (@2ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!35 (@3ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!36 (@4ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!37 (@defaultArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!38 (@0ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document V7)))))
                                (a!43 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm U7)
                                                                                  (@1HTMLForm U7)))))
                                (a!45 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!46 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!47 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!48 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!49 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!50 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document V7)))))
                                (a!56 (= (wd_document_domain D7)
                                         (SomeDomain (@0SomeDomain (wd_document_domain
                                                                     D7)))))
                                (a!57 (= (wd_document_domain Y6)
                                         (SomeDomain (@0SomeDomain (wd_document_domain
                                                                     Y6)))))
                                (a!59 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location D7)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location D7)))))
                                (a!60 (SomeOrigin (TupleOrigin (url_protocol (wd_location D7))
                                                               (url_host (wd_location D7))
                                                               (url_port (wd_location D7)))))
                                (a!61 (OpaqueOrigin (@0url_path_data (url_path (wd_location D7)))))
                                (a!63 (SomeOrigin (@0url_path_blob (url_path (wd_location D7)))))
                                (a!67 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location Y6)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location Y6)))))
                                (a!68 (SomeOrigin (TupleOrigin (url_protocol (wd_location Y6))
                                                               (url_host (wd_location Y6))
                                                               (url_port (wd_location Y6)))))
                                (a!69 (OpaqueOrigin (@0url_path_data (url_path (wd_location Y6)))))
                                (a!71 (SomeOrigin (@0url_path_blob (url_path (wd_location Y6)))))
                                (a!76 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!77 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!78 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!79 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!80 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!81 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M7)))))
                                (a!88 (DOMElementResource
                                        (wd_location I7)
                                        (ContentElementFrame
                                          (Build_Frame (frame_src J7) K7)
                                          (dc_html (wd_document L7)))))
                                (a!94 (@1ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!95 (@2ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!96 (@3ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!97 (@4ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!98 (@defaultArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!99 (@0ArrayoptionHTMLElement
                                        (html_body (dc_html (wd_document D7)))))
                                (a!104 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm C7)
                                                                                   (@1HTMLForm C7)))))
                                (a!106 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!107 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!108 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!109 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!110 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!111 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D7)))))
                                (a!116 (ite (= K7 3)
                                            (@3ArrayWindow (windows E7))
                                            (ite (= K7 4)
                                                 (@4ArrayWindow (windows E7))
                                                 (@defaultArrayWindow
                                                   (windows E7)))))
                                (a!119 (ite (= (frame_window J7) 3)
                                            (@3ArrayWindow (windows E7))
                                            (ite (= (frame_window J7) 4)
                                                 (@4ArrayWindow (windows E7))
                                                 (@defaultArrayWindow
                                                   (windows E7)))))
                                (a!123 (@1ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!124 (@2ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!125 (@3ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!126 (@4ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!127 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document Y8)))))
                                (a!128 (@0ArrayoptionInt (in_body (dc_init (wd_document Y8)))))
                                (a!134 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!135 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!136 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!137 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!138 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!139 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q8)))))
                                (a!146 (@1ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!147 (@2ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!148 (@3ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!149 (@4ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!150 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document G8)))))
                                (a!151 (@0ArrayoptionInt (in_body (dc_init (wd_document G8)))))
                                (a!156 (DOMElementResource
                                         (wd_location M8)
                                         (ContentElementFrame
                                           (Build_Frame (frame_src N8) O8)
                                           P8)))
                                (a!162 (ite (= O8 3)
                                            (@3ArrayWindow (windows H8))
                                            (ite (= O8 4)
                                                 (@4ArrayWindow (windows H8))
                                                 (@defaultArrayWindow
                                                   (windows H8)))))
                                (a!165 (ite (= (frame_window N8) 3)
                                            (@3ArrayWindow (windows H8))
                                            (ite (= (frame_window N8) 4)
                                                 (@4ArrayWindow (windows H8))
                                                 (@defaultArrayWindow
                                                   (windows H8)))))
                                (a!169 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!170 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!171 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!172 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!173 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!174 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E)))))
                                (a!181 (ite (= (frame_window G) 3)
                                            (@3ArrayWindow (windows L))
                                            (ite (= (frame_window G) 4)
                                                 (@4ArrayWindow (windows L))
                                                 (@defaultArrayWindow
                                                   (windows L)))))
                                (a!186 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!187 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!188 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!189 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!190 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document D1)))))
                                (a!191 (@defaultArrayoptionDOMElement
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
                                (a!220 (ite (= (frame_window L4) 3)
                                            (@3ArrayWindow (windows M4))
                                            (ite (= (frame_window L4) 4)
                                                 (@4ArrayWindow (windows M4))
                                                 (@defaultArrayWindow
                                                   (windows M4)))))
                                (a!223 (not (= (url_protocol (wd_location O4))
                                               ProtocolHTTPS)))
                                (a!226 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!227 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!228 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!229 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!230 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!231 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F4)))))
                                (a!238 (ite (= (frame_window E4) 3)
                                            (@3ArrayWindow (windows S4))
                                            (ite (= (frame_window E4) 4)
                                                 (@4ArrayWindow (windows S4))
                                                 (@defaultArrayWindow
                                                   (windows S4)))))
                                (a!242 (= (rp_hd_csp (dc_headers (wd_document A4)))
                                          NoneCSP))
                                (a!243 (or (= (tt_policy Y3) NoneoptionInt)
                                           (and (= W3 (SomeInt X3))
                                                (= (tt_policy Y3)
                                                   (SomeoptionInt W3)))))
                                (a!245 (= (rp_hd_csp (dc_headers (wd_document A4)))
                                          (SomeCSP Z3)))
                                (a!246 (and (= R1 P2)
                                            (= N2 (DOMPath nilInt O2))
                                            (= Q1 N2)
                                            (= (url_protocol (wd_location P2))
                                               ProtocolHTTPS)
                                            (= T1 M2)))
                                (a!247 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!248 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!249 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!250 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!251 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!252 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                (a!259 (ite (= (frame_window D2) 3)
                                            (@3ArrayWindow (windows H2))
                                            (ite (= (frame_window D2) 4)
                                                 (@4ArrayWindow (windows H2))
                                                 (@defaultArrayWindow
                                                   (windows H2)))))
                                (a!263 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!264 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!265 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!266 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!267 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!268 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document X2)))))
                                (a!275 (ite (= (frame_window Z2) 3)
                                            (@3ArrayWindow (windows E3))
                                            (ite (= (frame_window Z2) 4)
                                                 (@4ArrayWindow (windows E3))
                                                 (@defaultArrayWindow
                                                   (windows E3)))))
                                (a!280 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!281 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!282 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!283 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!284 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!285 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document U3)))))
                                (a!293 (= (rp_hd_csp (dc_headers (wd_document M6)))
                                          NoneCSP))
                                (a!294 (or (= (tt_policy K6) NoneoptionInt)
                                           (and (= I6 (SomeInt J6))
                                                (= (tt_policy K6)
                                                   (SomeoptionInt I6)))))
                                (a!296 (= (rp_hd_csp (dc_headers (wd_document M6)))
                                          (SomeCSP L6)))
                                (a!297 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!298 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!299 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!300 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!301 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!302 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document J5)))))
                                (a!309 (ite (= (frame_window L5) 3)
                                            (@3ArrayWindow (windows Q5))
                                            (ite (= (frame_window L5) 4)
                                                 (@4ArrayWindow (windows Q5))
                                                 (@defaultArrayWindow
                                                   (windows Q5)))))
                                (a!314 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!315 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!316 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!317 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!318 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!319 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G6)))))
                                (a!328 (= (rp_hd_csp (dc_headers (wd_document S1)))
                                          (SomeCSP O6))))
                          (let ((a!8 (ite (= Y 2)
                                          a!4
                                          (ite (= Y 3)
                                               a!5
                                               (ite (= Y 4) a!6 a!7))))
                                (a!15 (and (= (url_protocol (wd_location V7))
                                              (url_protocol (wd_location Q7)))
                                           a!13
                                           a!14
                                           (= (@0SomeDomain (wd_document_domain
                                                              V7))
                                              (@0SomeDomain (wd_document_domain
                                                              Q7)))))
                                (a!19 (ite ((_ is url_path_data)
                                             (url_path (wd_location V7)))
                                           (SomeOrigin a!18)
                                           NoneOrigin))
                                (a!21 (ite ((_ is url_path_blob)
                                             (url_path (wd_location V7)))
                                           a!20
                                           NoneOrigin))
                                (a!27 (ite ((_ is url_path_data)
                                             (url_path (wd_location Q7)))
                                           (SomeOrigin a!26)
                                           NoneOrigin))
                                (a!29 (ite ((_ is url_path_blob)
                                             (url_path (wd_location Q7)))
                                           a!28
                                           NoneOrigin))
                                (a!39 (ite (= T7 4)
                                           (Build_ArrayoptionHTMLElement
                                             a!38
                                             a!33
                                             a!34
                                             a!35
                                             (SomeHTMLElement U7)
                                             a!37)
                                           (html_body (dc_html (wd_document V7)))))
                                (a!44 (ite (or ((_ is HTMLImage) U7)
                                               ((_ is HTMLScript) U7))
                                           NoneDOMElement
                                           (ite ((_ is HTMLForm) U7)
                                                a!43
                                                NoneDOMElement)))
                                (a!58 (and (= (url_protocol (wd_location D7))
                                              (url_protocol (wd_location Y6)))
                                           a!56
                                           a!57
                                           (= (@0SomeDomain (wd_document_domain
                                                              D7))
                                              (@0SomeDomain (wd_document_domain
                                                              Y6)))))
                                (a!62 (ite ((_ is url_path_data)
                                             (url_path (wd_location D7)))
                                           (SomeOrigin a!61)
                                           NoneOrigin))
                                (a!64 (ite ((_ is url_path_blob)
                                             (url_path (wd_location D7)))
                                           a!63
                                           NoneOrigin))
                                (a!70 (ite ((_ is url_path_data)
                                             (url_path (wd_location Y6)))
                                           (SomeOrigin a!69)
                                           NoneOrigin))
                                (a!72 (ite ((_ is url_path_blob)
                                             (url_path (wd_location Y6)))
                                           a!71
                                           NoneOrigin))
                                (a!82 (ite (= H7 2)
                                           a!78
                                           (ite (= H7 3)
                                                a!79
                                                (ite (= H7 4) a!80 a!81))))
                                (a!89 (ite (= H7 4)
                                           (Build_ArrayoptionDOMElement
                                             a!76
                                             a!77
                                             a!78
                                             a!79
                                             (SomeDOMElement a!88)
                                             a!81)
                                           (dm_body (dc_dom (wd_document M7)))))
                                (a!100 (ite (= B7 4)
                                            (Build_ArrayoptionHTMLElement
                                              a!99
                                              a!94
                                              a!95
                                              a!96
                                              (SomeHTMLElement C7)
                                              a!98)
                                            (html_body (dc_html (wd_document D7)))))
                                (a!105 (ite (or ((_ is HTMLImage) C7)
                                                ((_ is HTMLScript) C7))
                                            NoneDOMElement
                                            (ite ((_ is HTMLForm) C7)
                                                 a!104
                                                 NoneDOMElement)))
                                (a!117 (ite (= K7 1)
                                            (@1ArrayWindow (windows E7))
                                            (ite (= K7 2)
                                                 (@2ArrayWindow (windows E7))
                                                 a!116)))
                                (a!120 (ite (= (frame_window J7) 1)
                                            (@1ArrayWindow (windows E7))
                                            (ite (= (frame_window J7) 2)
                                                 (@2ArrayWindow (windows E7))
                                                 a!119)))
                                (a!129 (ite (= W8 4)
                                            (Build_ArrayoptionInt
                                              a!128
                                              a!123
                                              a!124
                                              a!125
                                              X8
                                              a!127)
                                            (in_body (dc_init (wd_document Y8)))))
                                (a!140 (ite (= L8 2)
                                            a!136
                                            (ite (= L8 3)
                                                 a!137
                                                 (ite (= L8 4) a!138 a!139))))
                                (a!152 (ite (= E8 4)
                                            (Build_ArrayoptionInt
                                              a!151
                                              a!146
                                              a!147
                                              a!148
                                              F8
                                              a!150)
                                            (in_body (dc_init (wd_document G8)))))
                                (a!157 (ite (= L8 4)
                                            (Build_ArrayoptionDOMElement
                                              a!134
                                              a!135
                                              a!136
                                              a!137
                                              (SomeDOMElement a!156)
                                              a!139)
                                            (dm_body (dc_dom (wd_document Q8)))))
                                (a!163 (ite (= O8 1)
                                            (@1ArrayWindow (windows H8))
                                            (ite (= O8 2)
                                                 (@2ArrayWindow (windows H8))
                                                 a!162)))
                                (a!166 (ite (= (frame_window N8) 1)
                                            (@1ArrayWindow (windows H8))
                                            (ite (= (frame_window N8) 2)
                                                 (@2ArrayWindow (windows H8))
                                                 a!165)))
                                (a!175 (ite (= D 2)
                                            a!171
                                            (ite (= D 3)
                                                 a!172
                                                 (ite (= D 4) a!173 a!174))))
                                (a!182 (ite (= (frame_window G) 1)
                                            (@1ArrayWindow (windows L))
                                            (ite (= (frame_window G) 2)
                                                 (@2ArrayWindow (windows L))
                                                 a!181)))
                                (a!192 (ite (= C1 2)
                                            a!188
                                            (ite (= C1 3)
                                                 a!189
                                                 (ite (= C1 4) a!190 a!191))))
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
                                (a!221 (ite (= (frame_window L4) 1)
                                            (@1ArrayWindow (windows M4))
                                            (ite (= (frame_window L4) 2)
                                                 (@2ArrayWindow (windows M4))
                                                 a!220)))
                                (a!232 (ite (= C4 2)
                                            a!228
                                            (ite (= C4 3)
                                                 a!229
                                                 (ite (= C4 4) a!230 a!231))))
                                (a!239 (ite (= (frame_window E4) 1)
                                            (@1ArrayWindow (windows S4))
                                            (ite (= (frame_window E4) 2)
                                                 (@2ArrayWindow (windows S4))
                                                 a!238)))
                                (a!244 (or (= (csp_trusted_types Z3)
                                              NoneTrustedTypes)
                                           (and a!243
                                                (= (csp_trusted_types Z3)
                                                   (SomeTrustedTypes Y3)))))
                                (a!253 (ite (= A2 2)
                                            a!249
                                            (ite (= A2 3)
                                                 a!250
                                                 (ite (= A2 4) a!251 a!252))))
                                (a!260 (ite (= (frame_window D2) 1)
                                            (@1ArrayWindow (windows H2))
                                            (ite (= (frame_window D2) 2)
                                                 (@2ArrayWindow (windows H2))
                                                 a!259)))
                                (a!269 (ite (= W2 2)
                                            a!265
                                            (ite (= W2 3)
                                                 a!266
                                                 (ite (= W2 4) a!267 a!268))))
                                (a!276 (ite (= (frame_window Z2) 1)
                                            (@1ArrayWindow (windows E3))
                                            (ite (= (frame_window Z2) 2)
                                                 (@2ArrayWindow (windows E3))
                                                 a!275)))
                                (a!286 (ite (= T3 2)
                                            a!282
                                            (ite (= T3 3)
                                                 a!283
                                                 (ite (= T3 4) a!284 a!285))))
                                (a!295 (or (= (csp_trusted_types L6)
                                              NoneTrustedTypes)
                                           (and a!294
                                                (= (csp_trusted_types L6)
                                                   (SomeTrustedTypes K6)))))
                                (a!303 (ite (= I5 2)
                                            a!299
                                            (ite (= I5 3)
                                                 a!300
                                                 (ite (= I5 4) a!301 a!302))))
                                (a!310 (ite (= (frame_window L5) 1)
                                            (@1ArrayWindow (windows Q5))
                                            (ite (= (frame_window L5) 2)
                                                 (@2ArrayWindow (windows Q5))
                                                 a!309)))
                                (a!320 (ite (= F6 2)
                                            a!316
                                            (ite (= F6 3)
                                                 a!317
                                                 (ite (= F6 4) a!318 a!319)))))
                          (let ((a!9 (ite (= Y 0) a!2 (ite (= Y 1) a!3 a!8)))
                                (a!22 (ite ((_ is url_path_data)
                                             (url_path (wd_location V7)))
                                           NoneOrigin
                                           a!21))
                                (a!30 (ite ((_ is url_path_data)
                                             (url_path (wd_location Q7)))
                                           NoneOrigin
                                           a!29))
                                (a!40 (ite (= T7 2)
                                           (Build_ArrayoptionHTMLElement
                                             a!38
                                             a!33
                                             (SomeHTMLElement U7)
                                             a!35
                                             a!36
                                             a!37)
                                           (ite (= T7 3)
                                                (Build_ArrayoptionHTMLElement
                                                  a!38
                                                  a!33
                                                  a!34
                                                  (SomeHTMLElement U7)
                                                  a!36
                                                  a!37)
                                                a!39)))
                                (a!51 (ite (= T7 4)
                                           (Build_ArrayoptionDOMElement
                                             a!50
                                             a!45
                                             a!46
                                             a!47
                                             a!44
                                             a!49)
                                           (dm_body (dc_dom (wd_document V7)))))
                                (a!65 (ite ((_ is url_path_data)
                                             (url_path (wd_location D7)))
                                           NoneOrigin
                                           a!64))
                                (a!73 (ite ((_ is url_path_data)
                                             (url_path (wd_location Y6)))
                                           NoneOrigin
                                           a!72))
                                (a!83 (ite (= H7 0)
                                           a!76
                                           (ite (= H7 1) a!77 a!82)))
                                (a!90 (ite (= H7 2)
                                           (Build_ArrayoptionDOMElement
                                             a!76
                                             a!77
                                             (SomeDOMElement a!88)
                                             a!79
                                             a!80
                                             a!81)
                                           (ite (= H7 3)
                                                (Build_ArrayoptionDOMElement
                                                  a!76
                                                  a!77
                                                  a!78
                                                  (SomeDOMElement a!88)
                                                  a!80
                                                  a!81)
                                                a!89)))
                                (a!101 (ite (= B7 2)
                                            (Build_ArrayoptionHTMLElement
                                              a!99
                                              a!94
                                              (SomeHTMLElement C7)
                                              a!96
                                              a!97
                                              a!98)
                                            (ite (= B7 3)
                                                 (Build_ArrayoptionHTMLElement
                                                   a!99
                                                   a!94
                                                   a!95
                                                   (SomeHTMLElement C7)
                                                   a!97
                                                   a!98)
                                                 a!100)))
                                (a!112 (ite (= B7 4)
                                            (Build_ArrayoptionDOMElement
                                              a!111
                                              a!106
                                              a!107
                                              a!108
                                              a!105
                                              a!110)
                                            (dm_body (dc_dom (wd_document D7)))))
                                (a!118 (= (ite (= K7 0)
                                               (@0ArrayWindow (windows E7))
                                               a!117)
                                          L7))
                                (a!121 (= (ite (= (frame_window J7) 0)
                                               (@0ArrayWindow (windows E7))
                                               a!120)
                                          I7))
                                (a!130 (ite (= W8 1)
                                            (Build_ArrayoptionInt
                                              a!128
                                              X8
                                              a!124
                                              a!125
                                              a!126
                                              a!127)
                                            (ite (= W8 2)
                                                 (Build_ArrayoptionInt
                                                   a!128
                                                   a!123
                                                   X8
                                                   a!125
                                                   a!126
                                                   a!127)
                                                 (ite (= W8 3)
                                                      (Build_ArrayoptionInt
                                                        a!128
                                                        a!123
                                                        a!124
                                                        X8
                                                        a!126
                                                        a!127)
                                                      a!129))))
                                (a!141 (ite (= L8 0)
                                            a!134
                                            (ite (= L8 1) a!135 a!140)))
                                (a!153 (ite (= E8 1)
                                            (Build_ArrayoptionInt
                                              a!151
                                              F8
                                              a!147
                                              a!148
                                              a!149
                                              a!150)
                                            (ite (= E8 2)
                                                 (Build_ArrayoptionInt
                                                   a!151
                                                   a!146
                                                   F8
                                                   a!148
                                                   a!149
                                                   a!150)
                                                 (ite (= E8 3)
                                                      (Build_ArrayoptionInt
                                                        a!151
                                                        a!146
                                                        a!147
                                                        F8
                                                        a!149
                                                        a!150)
                                                      a!152))))
                                (a!158 (ite (= L8 2)
                                            (Build_ArrayoptionDOMElement
                                              a!134
                                              a!135
                                              (SomeDOMElement a!156)
                                              a!137
                                              a!138
                                              a!139)
                                            (ite (= L8 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!134
                                                   a!135
                                                   a!136
                                                   (SomeDOMElement a!156)
                                                   a!138
                                                   a!139)
                                                 a!157)))
                                (a!164 (= (ite (= O8 0)
                                               (@0ArrayWindow (windows H8))
                                               a!163)
                                          I8))
                                (a!167 (= (ite (= (frame_window N8) 0)
                                               (@0ArrayWindow (windows H8))
                                               a!166)
                                          M8))
                                (a!176 (ite (= D 0)
                                            a!169
                                            (ite (= D 1) a!170 a!175)))
                                (a!183 (= (ite (= (frame_window G) 0)
                                               (@0ArrayWindow (windows L))
                                               a!182)
                                          J))
                                (a!193 (ite (= C1 0)
                                            a!186
                                            (ite (= C1 1) a!187 a!192)))
                                (a!200 (= (ite (= (frame_window F1) 0)
                                               (@0ArrayWindow (windows K1))
                                               a!199)
                                          I1))
                                (a!215 (ite (= J4 0)
                                            a!208
                                            (ite (= J4 1) a!209 a!214)))
                                (a!222 (= (ite (= (frame_window L4) 0)
                                               (@0ArrayWindow (windows M4))
                                               a!221)
                                          N4))
                                (a!233 (ite (= C4 0)
                                            a!226
                                            (ite (= C4 1) a!227 a!232)))
                                (a!240 (= (ite (= (frame_window E4) 0)
                                               (@0ArrayWindow (windows S4))
                                               a!239)
                                          R4))
                                (a!254 (ite (= A2 0)
                                            a!247
                                            (ite (= A2 1) a!248 a!253)))
                                (a!261 (= (ite (= (frame_window D2) 0)
                                               (@0ArrayWindow (windows H2))
                                               a!260)
                                          G2))
                                (a!270 (ite (= W2 0)
                                            a!263
                                            (ite (= W2 1) a!264 a!269)))
                                (a!277 (= (ite (= (frame_window Z2) 0)
                                               (@0ArrayWindow (windows E3))
                                               a!276)
                                          C3))
                                (a!287 (ite (= T3 0)
                                            a!280
                                            (ite (= T3 1) a!281 a!286)))
                                (a!304 (ite (= I5 0)
                                            a!297
                                            (ite (= I5 1) a!298 a!303)))
                                (a!311 (= (ite (= (frame_window L5) 0)
                                               (@0ArrayWindow (windows Q5))
                                               a!310)
                                          O5))
                                (a!321 (ite (= F6 0)
                                            a!314
                                            (ite (= F6 1) a!315 a!320))))
                          (let ((a!10 (= (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!9)))
                                         A1))
                                (a!11 (ContentElementScript
                                        (@0ContentElementScript
                                          (@1DOMElementResource
                                            (@0SomeDOMElement a!9)))))
                                (a!12 (= (@0SomeDOMElement a!9)
                                         (DOMElementResource
                                           (@0DOMElementResource
                                             (@0SomeDOMElement a!9))
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!9)))))
                                (a!23 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location V7)))
                                           a!19
                                           a!22))
                                (a!31 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location Q7)))
                                           a!27
                                           a!30))
                                (a!41 (ite (= T7 0)
                                           (Build_ArrayoptionHTMLElement
                                             (SomeHTMLElement U7)
                                             a!33
                                             a!34
                                             a!35
                                             a!36
                                             a!37)
                                           (ite (= T7 1)
                                                (Build_ArrayoptionHTMLElement
                                                  a!38
                                                  (SomeHTMLElement U7)
                                                  a!34
                                                  a!35
                                                  a!36
                                                  a!37)
                                                a!40)))
                                (a!52 (ite (= T7 1)
                                           (Build_ArrayoptionDOMElement
                                             a!50
                                             a!44
                                             a!46
                                             a!47
                                             a!48
                                             a!49)
                                           (ite (= T7 2)
                                                (Build_ArrayoptionDOMElement
                                                  a!50
                                                  a!45
                                                  a!44
                                                  a!47
                                                  a!48
                                                  a!49)
                                                (ite (= T7 3)
                                                     (Build_ArrayoptionDOMElement
                                                       a!50
                                                       a!45
                                                       a!46
                                                       a!44
                                                       a!48
                                                       a!49)
                                                     a!51))))
                                (a!66 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location D7)))
                                           a!62
                                           a!65))
                                (a!74 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location Y6)))
                                           a!70
                                           a!73))
                                (a!84 (= (@0SomeDOMElement a!83)
                                         (DOMElementResource
                                           (@0DOMElementResource
                                             (@0SomeDOMElement a!83))
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!83)))))
                                (a!85 (ContentElementFrame
                                        (@0ContentElementFrame
                                          (@1DOMElementResource
                                            (@0SomeDOMElement a!83)))
                                        (@1ContentElementFrame
                                          (@1DOMElementResource
                                            (@0SomeDOMElement a!83)))))
                                (a!86 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!83)))
                                         J7))
                                (a!87 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!83)))
                                         R6))
                                (a!91 (ite (= H7 0)
                                           (Build_ArrayoptionDOMElement
                                             (SomeDOMElement a!88)
                                             a!77
                                             a!78
                                             a!79
                                             a!80
                                             a!81)
                                           (ite (= H7 1)
                                                (Build_ArrayoptionDOMElement
                                                  a!76
                                                  (SomeDOMElement a!88)
                                                  a!78
                                                  a!79
                                                  a!80
                                                  a!81)
                                                a!90)))
                                (a!102 (ite (= B7 0)
                                            (Build_ArrayoptionHTMLElement
                                              (SomeHTMLElement C7)
                                              a!94
                                              a!95
                                              a!96
                                              a!97
                                              a!98)
                                            (ite (= B7 1)
                                                 (Build_ArrayoptionHTMLElement
                                                   a!99
                                                   (SomeHTMLElement C7)
                                                   a!95
                                                   a!96
                                                   a!97
                                                   a!98)
                                                 a!101)))
                                (a!113 (ite (= B7 1)
                                            (Build_ArrayoptionDOMElement
                                              a!111
                                              a!105
                                              a!107
                                              a!108
                                              a!109
                                              a!110)
                                            (ite (= B7 2)
                                                 (Build_ArrayoptionDOMElement
                                                   a!111
                                                   a!106
                                                   a!105
                                                   a!108
                                                   a!109
                                                   a!110)
                                                 (ite (= B7 3)
                                                      (Build_ArrayoptionDOMElement
                                                        a!111
                                                        a!106
                                                        a!107
                                                        a!105
                                                        a!109
                                                        a!110)
                                                      a!112))))
                                (a!131 (Build_Initiators (in_toplevel (dc_init (wd_document Y8)))
                                                         (ite (= W8 0)
                                                              (Build_ArrayoptionInt
                                                                X8
                                                                a!123
                                                                a!124
                                                                a!125
                                                                a!126
                                                                a!127)
                                                              a!130)))
                                (a!142 (= (@0SomeDOMElement a!141)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!141))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!141)))))
                                (a!143 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!141)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!141)))))
                                (a!144 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!141)))
                                          N8))
                                (a!145 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!141)))
                                          P8))
                                (a!154 (Build_Initiators (in_toplevel (dc_init (wd_document G8)))
                                                         (ite (= E8 0)
                                                              (Build_ArrayoptionInt
                                                                F8
                                                                a!146
                                                                a!147
                                                                a!148
                                                                a!149
                                                                a!150)
                                                              a!153)))
                                (a!159 (ite (= L8 0)
                                            (Build_ArrayoptionDOMElement
                                              (SomeDOMElement a!156)
                                              a!135
                                              a!136
                                              a!137
                                              a!138
                                              a!139)
                                            (ite (= L8 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!134
                                                   (SomeDOMElement a!156)
                                                   a!136
                                                   a!137
                                                   a!138
                                                   a!139)
                                                 a!158)))
                                (a!177 (= (@0SomeDOMElement a!176)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!176))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!176)))))
                                (a!178 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!176)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!176)))))
                                (a!179 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!176)))
                                          G))
                                (a!180 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!176)))
                                          F))
                                (a!194 (= (@0SomeDOMElement a!193)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!193))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!193)))))
                                (a!195 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!193)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!193)))))
                                (a!196 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!193)))
                                          F1))
                                (a!197 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!193)))
                                          E1))
                                (a!216 (= (@0SomeDOMElement a!215)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!215))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!215)))))
                                (a!217 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!215)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!215)))))
                                (a!218 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!215)))
                                          L4))
                                (a!219 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!215)))
                                          K4))
                                (a!234 (= (@0SomeDOMElement a!233)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!233))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!233)))))
                                (a!235 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!233)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!233)))))
                                (a!236 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!233)))
                                          E4))
                                (a!237 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!233)))
                                          D4))
                                (a!255 (= (@0SomeDOMElement a!254)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!254))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!254)))))
                                (a!256 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!254)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!254)))))
                                (a!257 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!254)))
                                          D2))
                                (a!258 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!254)))
                                          C2))
                                (a!271 (= (@0SomeDOMElement a!270)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!270))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!270)))))
                                (a!272 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!270)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!270)))))
                                (a!273 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!270)))
                                          Z2))
                                (a!274 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!270)))
                                          Y2))
                                (a!288 (= (@0SomeDOMElement a!287)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!287))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!287)))))
                                (a!289 (ContentElementScript
                                         (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!287)))))
                                (a!290 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!287)))
                                          V3))
                                (a!305 (= (@0SomeDOMElement a!304)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!304))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!304)))))
                                (a!306 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!304)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!304)))))
                                (a!307 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!304)))
                                          L5))
                                (a!308 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!304)))
                                          K5))
                                (a!322 (= (@0SomeDOMElement a!321)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!321))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!321)))))
                                (a!323 (ContentElementScript
                                         (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!321)))))
                                (a!324 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!321)))
                                          H6)))
                          (let ((a!32 (and (not (= (ite a!16 a!17 a!23)
                                                   NoneOrigin))
                                           (= (ite a!16 a!17 a!23)
                                              (ite a!24 a!25 a!31))
                                           (= (wd_document_domain V7)
                                              NoneDomain)
                                           (= (wd_document_domain Q7)
                                              NoneDomain)))
                                (a!42 (Build_HTML (html_nonce (dc_html (wd_document V7)))
                                                  (html_head (dc_html (wd_document V7)))
                                                  a!41))
                                (a!53 (Build_DOM (dm_nonce (dc_dom (wd_document V7)))
                                                 (dm_head (dc_dom (wd_document V7)))
                                                 (ite (= T7 0)
                                                      (Build_ArrayoptionDOMElement
                                                        a!44
                                                        a!45
                                                        a!46
                                                        a!47
                                                        a!48
                                                        a!49)
                                                      a!52)))
                                (a!75 (and (not (= (ite a!59 a!60 a!66)
                                                   NoneOrigin))
                                           (= (ite a!59 a!60 a!66)
                                              (ite a!67 a!68 a!74))
                                           (= (wd_document_domain D7)
                                              NoneDomain)
                                           (= (wd_document_domain Y6)
                                              NoneDomain)))
                                (a!92 (Build_DOM (dm_nonce (dc_dom (wd_document M7)))
                                                 (dm_head (dc_dom (wd_document M7)))
                                                 a!91))
                                (a!103 (Build_HTML (html_nonce (dc_html (wd_document D7)))
                                                   (html_head (dc_html (wd_document D7)))
                                                   a!102))
                                (a!114 (Build_DOM (dm_nonce (dc_dom (wd_document D7)))
                                                  (dm_head (dc_dom (wd_document D7)))
                                                  (ite (= B7 0)
                                                       (Build_ArrayoptionDOMElement
                                                         a!105
                                                         a!106
                                                         a!107
                                                         a!108
                                                         a!109
                                                         a!110)
                                                       a!113)))
                                (a!132 (Build_Window (wd_nonce Y8)
                                                     (wd_parent Y8)
                                                     (wd_location Y8)
                                                     (wd_document_domain Y8)
                                                     (Build_Document (dc_version (wd_document Y8))
                                                                     (dc_nonce (wd_document Y8))
                                                                     (dc_headers (wd_document Y8))
                                                                     (dc_html (wd_document Y8))
                                                                     (dc_dom (wd_document Y8))
                                                                     a!131)))
                                (a!155 (Build_Window (wd_nonce G8)
                                                     (wd_parent G8)
                                                     (wd_location G8)
                                                     (wd_document_domain G8)
                                                     (Build_Document (dc_version (wd_document G8))
                                                                     (dc_nonce (wd_document G8))
                                                                     (dc_headers (wd_document G8))
                                                                     (dc_html (wd_document G8))
                                                                     (dc_dom (wd_document G8))
                                                                     a!154)))
                                (a!160 (Build_DOM (dm_nonce (dc_dom (wd_document Q8)))
                                                  (dm_head (dc_dom (wd_document Q8)))
                                                  a!159))
                                (a!184 (and (= a!176
                                               (SomeDOMElement (@0SomeDOMElement a!176)))
                                            a!177
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!176))
                                               a!178)
                                            a!179
                                            a!180
                                            (= R1 E)
                                            (= Z K)
                                            (= P Q)
                                            (= K P)
                                            (= J Q)
                                            a!183
                                            (= W C)
                                            (= N (DOMPath H I))
                                            (= N (DOMPath nilInt O))
                                            (= C (DOMPath (consInt D H) I))
                                            (= T1 L)
                                            (= L M)))
                                (a!201 (and (= a!193
                                               (SomeDOMElement (@0SomeDOMElement a!193)))
                                            a!194
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!193))
                                               a!195)
                                            a!196
                                            a!197
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
                                (a!224 (and (= a!215
                                               (SomeDOMElement (@0SomeDOMElement a!215)))
                                            a!216
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!215))
                                               a!217)
                                            a!218
                                            a!219
                                            (= R4 O4)
                                            a!222
                                            (= G4 (DOMPath P4 Q4))
                                            (= G4 (DOMPath (consInt J4 H4) I4))
                                            a!223
                                            (= S4 M4)))
                                (a!262 (and (= a!254
                                               (SomeDOMElement (@0SomeDOMElement a!254)))
                                            a!255
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!254))
                                               a!256)
                                            a!257
                                            a!258
                                            (= R1 B2)
                                            (= G2 L2)
                                            a!261
                                            (= J2 (DOMPath E2 F2))
                                            (= J2 (DOMPath nilInt K2))
                                            (= Z1 (DOMPath (consInt A2 E2) F2))
                                            (= Q1 Z1)
                                            (= (url_protocol (wd_location L2))
                                               ProtocolHTTPS)
                                            (= (url_protocol (wd_location B2))
                                               ProtocolHTTPS)
                                            (= H2 I2)
                                            (= T1 H2)))
                                (a!278 (and (= a!270
                                               (SomeDOMElement (@0SomeDOMElement a!270)))
                                            a!271
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!270))
                                               a!272)
                                            a!273
                                            a!274
                                            (= I3 J3)
                                            (= D3 I3)
                                            (= C3 J3)
                                            (= U3 D3)
                                            (= K3 X2)
                                            a!277
                                            (= G3 (DOMPath A3 B3))
                                            (= G3 (DOMPath nilInt H3))
                                            (= R3 V2)
                                            (= V2 (DOMPath (consInt W2 A3) B3))
                                            (= E3 F3)
                                            (= L3 E3)))
                                (a!312 (and (= a!304
                                               (SomeDOMElement (@0SomeDOMElement a!304)))
                                            a!305
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!304))
                                               a!306)
                                            a!307
                                            a!308
                                            (= G6 P5)
                                            (= W5 J5)
                                            (= P5 U5)
                                            (= O5 V5)
                                            (= U5 V5)
                                            a!311
                                            (= S5 (DOMPath M5 N5))
                                            (= S5 (DOMPath nilInt T5))
                                            (= H5 (DOMPath (consInt I5 M5) N5))
                                            (= D6 H5)
                                            (= Q5 R5)
                                            (= X5 Q5))))
                          (let ((a!54 (Build_Window (wd_nonce V7)
                                                    (wd_parent V7)
                                                    (wd_location V7)
                                                    (wd_document_domain V7)
                                                    (Build_Document (+ 1 S7)
                                                                    (dc_nonce (wd_document V7))
                                                                    (dc_headers (wd_document V7))
                                                                    a!42
                                                                    a!53
                                                                    (dc_init (wd_document V7)))))
                                (a!93 (Build_Window (wd_nonce M7)
                                                    (wd_parent M7)
                                                    (wd_location M7)
                                                    (wd_document_domain M7)
                                                    (Build_Document (+ 1 G7)
                                                                    (dc_nonce (wd_document M7))
                                                                    (dc_headers (wd_document M7))
                                                                    (dc_html (wd_document M7))
                                                                    a!92
                                                                    (dc_init (wd_document M7)))))
                                (a!115 (Build_Window (wd_nonce D7)
                                                     (wd_parent D7)
                                                     (wd_location D7)
                                                     (wd_document_domain D7)
                                                     (Build_Document (+ 1 A7)
                                                                     (dc_nonce (wd_document D7))
                                                                     (dc_headers (wd_document D7))
                                                                     a!103
                                                                     a!114
                                                                     (dc_init (wd_document D7)))))
                                (a!133 (and (= A9 S8)
                                            (= D9 V8)
                                            (= R8 Y8)
                                            (= V8 a!132)
                                            (= U8
                                               (DOMPath nilInt (DOMIndex W8)))
                                            (= Q1 U8)
                                            (= X8 NoneInt)
                                            (= T1 T8)))
                                (a!161 (Build_Window (wd_nonce Q8)
                                                     (wd_parent Q8)
                                                     (wd_location Q8)
                                                     (wd_document_domain Q8)
                                                     (Build_Document (+ 1 K8)
                                                                     (dc_nonce (wd_document Q8))
                                                                     (dc_headers (wd_document Q8))
                                                                     (dc_html (wd_document Q8))
                                                                     a!160
                                                                     (dc_init (wd_document Q8)))))
                                (a!185 (or (and (= R1 V)
                                                (= Z U)
                                                (= U V)
                                                (= W S)
                                                (= S (DOMPath nilInt T))
                                                (= T1 R))
                                           a!184))
                                (a!202 (or (and (= R1 Y1)
                                                (= X1 Y1)
                                                (= S1 X1)
                                                (= V1 (DOMPath nilInt W1))
                                                (= Q1 V1)
                                                (= T1 U1))
                                           a!201))
                                (a!225 (or a!206
                                           (and (= R4 W4)
                                                (= U4 (DOMPath P4 Q4))
                                                (= U4 (DOMPath nilInt V4))
                                                a!207
                                                (= S4 T4))
                                           a!224))
                                (a!279 (or (and (= U3 P3)
                                                (= P3 Q3)
                                                (= K3 Q3)
                                                (= R3 N3)
                                                (= N3 (DOMPath nilInt O3))
                                                (= L3 M3))
                                           a!278))
                                (a!313 (or (and (= G6 B6)
                                                (= B6 C6)
                                                (= W5 C6)
                                                (= Z5 (DOMPath nilInt A6))
                                                (= D6 Z5)
                                                (= X5 Y5))
                                           a!312)))
                          (let ((a!55 (and (or a!15 a!32)
                                           (= A9 S7)
                                           (= R7 a!54)
                                           (= R8 R7)
                                           (= R1 V7)
                                           (= Z Q7)
                                           (= P7 (DOMPath nilInt (DOMIndex T7)))
                                           (= Q1 P7)
                                           (= T1 O7)
                                           (= N7 U7)))
                                (a!122 (and (or a!58 a!75)
                                            (= A9 G7)
                                            (= G7 A7)
                                            (= a!83
                                               (SomeDOMElement (@0SomeDOMElement a!83)))
                                            a!84
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!83))
                                               a!85)
                                            a!86
                                            a!87
                                            (= L7 Z6)
                                            (= F7 a!93)
                                            (= I7 D7)
                                            (= R8 F7)
                                            (= Z6 a!115)
                                            (= R1 M7)
                                            (= V6 Y6)
                                            (= Z V6)
                                            a!118
                                            a!121
                                            (= Q6 (DOMPath (consInt H7 S6) T6))
                                            (= X6 (DOMPath S6 T6))
                                            (= X6
                                               (DOMPath nilInt (DOMIndex B7)))
                                            (= Q1 Q6)
                                            (= E7 W6)
                                            (= T1 E7)
                                            (= N7 U6)
                                            (= U6 C7)))
                                (a!168 (and (= A9 K8)
                                            (= K8 A8)
                                            (= a!141
                                               (SomeDOMElement (@0SomeDOMElement a!141)))
                                            a!142
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!141))
                                               a!143)
                                            a!144
                                            a!145
                                            (= D9 J8)
                                            (= D8 a!155)
                                            (= R8 Q8)
                                            (= M8 G8)
                                            (= I8 D8)
                                            (= J8 a!161)
                                            a!164
                                            a!167
                                            (= W7 (DOMPath (consInt L8 X7) Y7))
                                            (= C8 (DOMPath X7 Y7))
                                            (= C8
                                               (DOMPath nilInt (DOMIndex E8)))
                                            (= Q1 W7)
                                            (= Z7 F8)
                                            (= Z7 NoneInt)
                                            (= H8 B8)
                                            (= T1 H8)))
                                (a!241 (and a!225
                                            (= a!233
                                               (SomeDOMElement (@0SomeDOMElement a!233)))
                                            a!234
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!233))
                                               a!235)
                                            a!236
                                            a!237
                                            (= R1 F4)
                                            a!240
                                            (= B4 (DOMPath (consInt C4 P4) Q4))
                                            (= Q1 B4)
                                            (= T1 S4)))
                                (a!291 (and (or a!242 (and a!244 a!245))
                                            (or a!246 a!262)
                                            a!279
                                            (= a!287
                                               (SomeDOMElement (@0SomeDOMElement a!287)))
                                            a!288
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!287))
                                               a!289)
                                            (= P6 A4)
                                            (= A4 U3)
                                            (= K3 (st_window T2))
                                            (= R2 V3)
                                            (= A1 R2)
                                            a!290
                                            (= R3 (DOMPath S3 (DOMIndex T3)))
                                            (= S2 R3)
                                            (= U2 L3)
                                            (= T1 U2)
                                            (= N7 Q2)
                                            (= C5 T2)))
                                (a!325 (and (or a!293 (and a!295 a!296))
                                            a!313
                                            (not (c_restrict_tt_to_secure_contexts
                                                   (config T1)))
                                            (= a!321
                                               (SomeDOMElement (@0SomeDOMElement a!321)))
                                            a!322
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!321))
                                               a!323)
                                            (= M6 G6)
                                            (= P6 M6)
                                            (= W5 (st_window F5))
                                            (= D5 H6)
                                            (= A1 D5)
                                            a!324
                                            (= E5 D6)
                                            (= D6 (DOMPath E6 (DOMIndex F6)))
                                            (= G5 X5)
                                            (= T1 G5)
                                            (= N7 B5)
                                            (= C5 F5))))
                          (let ((a!292 (or (and (= R1 A5)
                                                (= Y4 (DOMPath nilInt Z4))
                                                (= Q1 Y4)
                                                a!205
                                                (= T1 X4))
                                           a!241
                                           a!291)))
                          (let ((a!326 (or (and a!292
                                                (c_restrict_tt_to_secure_contexts
                                                  (config T1)))
                                           a!325)))
                          (let ((a!327 (and (or (not (tt_require_for_script N6))
                                                (and a!326
                                                     (tt_require_for_script N6)))
                                            (= (csp_trusted_types O6)
                                               (SomeTrustedTypes N6)))))
                          (let ((a!329 (and (or (= (csp_trusted_types O6)
                                                   NoneTrustedTypes)
                                                a!327)
                                            a!328)))
                          (let ((a!330 (and (Reachable T1 Z8 C5)
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
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!9))
                                               a!11)
                                            a!12
                                            (= a!9
                                               (SomeDOMElement (@0SomeDOMElement a!9)))
                                            (or a!55 a!122)
                                            (or a!133 a!168)
                                            a!185
                                            a!202
                                            a!203
                                            (or a!204 a!329)
                                            (= B
                                               (consEvent (EvScriptUpdateHTML
                                                            W
                                                            Q1
                                                            S1)
                                                          Z8)))))
                            (=> a!330 (Reachable T1 B A))))))))))))))
                          :weight 0))))
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
      (a!7 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 21 22))
                      (SomeInt 23)
                      (url_path_res (anypath 24))))
      (a!9 (SomeTrustedTypes (Build_TrustedTypes
                               (SomeoptionInt (SomeInt 44301))
                               false)))
      (a!11 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 44084
                            44085
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!12 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 44102))
                                false)))
      (a!14 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 43892
                            43893
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!15 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 24446))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 44453)
                                  (url_path_data 44150 44151)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!16 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 44684
                            44685
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!17 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 44957
                            44958
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!19 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                (SomeTrustedTypes (Build_TrustedTypes
                                                    NoneoptionInt
                                                    false)))))
      (a!20 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 43688
                            43689
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!22 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 NoneoptionInt
                                                 45106
                                                 (SomeInt 48218)
                                                 NonePath))
                       NoneTrustedTypes))
      (a!26 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 47811)
                                                    (url_path_data 45824 45825))
                                         44719)))
      (a!27 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 48088)
                                                    (url_path_data 47622 47623))
                                         44503)))
      (a!28 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 45465)
                                                   (url_path_data 45352 45353)))))
      (a!29 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 45172)
                                                   (url_path_data 47480 47481)))))
      (a!30 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 46028)
                                                   (url_path_data 47053 47054)))))
      (a!32 (Build_Document 7730
                            7731
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 7726
                                        7727
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 7728
                                       7729
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 32384)
                                              (Build_ArrayoptionInt
                                                (SomeInt 39765)
                                                (SomeInt 17617)
                                                (SomeInt 20802)
                                                (SomeInt 41888)
                                                (SomeInt 27332)
                                                (SomeInt 17658)))))
      (a!33 (Build_URL ProtocolHTTP
                       (SomeDomain (subdomain 30 31))
                       (SomeInt 32)
                       (url_path_res (anypath 45))))
      (a!34 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 123))
                                false)))
      (a!37 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 63)
                                                   (url_path_data 64 65)))))
      (a!38 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 66)
                                                   (url_path_data 67 68)))))
      (a!39 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 60)
                                                  (url_path_data 61 62)))))
      (a!41 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 60)
                                                   (url_path_data 61 62)))))
      (a!45 (Build_Document 7737
                            7738
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 7733
                                        7734
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 7735
                                       7736
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 28151)
                                              (Build_ArrayoptionInt
                                                (SomeInt 42254)
                                                (SomeInt 30035)
                                                (SomeInt 41043)
                                                (SomeInt 20657)
                                                (SomeInt 29050)
                                                (SomeInt 14838)))))
      (a!46 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 44806))
                                false)))
      (a!48 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 45956)
                                                   (url_path_data 47334 47335)))))
      (a!49 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 47096)
                                                   (url_path_data 45202 45203)))))
      (a!52 (Build_ArrayContentElement
              (ContentElementHTML
                (Build_HTML 14457
                            14458
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 28396
                            28397
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 30314
                            30315
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 14555
                            14556
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 19793
                            19794
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 16813
                            16814
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!55 (Build_URL ProtocolHTTP
                       (SomeDomain (subdomain 30 31))
                       (SomeInt 32)
                       (url_path_res (anypath 33))))
      (a!56 (SomeSetCookie (Build_SetCookie (NoPrefix 34)
                                            35
                                            NoneDomain
                                            (subdomain 30 31)
                                            (anypath 36)
                                            false
                                            false
                                            SSStrict)))
      (a!57 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                      (SomeoptionInt (SomeInt 37))
                                      38
                                      NoneInt
                                      NonePath)))
      (a!58 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 39))
                                false)))
      (a!60 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 46)
                                                   (url_path_data 47 48)))))
      (a!61 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 49)
                                                  (url_path_data 50 51)))))
      (a!62 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 52)
                                                  (url_path_data 53 54)))))
      (a!63 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 99)
                                                   (url_path_data 100 101)))))
      (a!64 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 42)
                                                  (url_path_data 43 44)))))
      (a!72 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 3) 1))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 3))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 2907))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!75 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 49)
                                                   (url_path_data 50 51)))))
      (a!76 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 52)
                                                   (url_path_data 53 54)))))
      (a!77 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 42)
                                                   (url_path_data 43 44)))))
      (a!80 (SomeHTMLElement (HTMLScript (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 34063)
                                                    (url_path_data 15847 15848)))))
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
                                 (a!2 (ContentElementHTML
                                        (@0ContentElementHTML
                                          (@0SomeContentElement (rp_content R1)))))
                                 (a!3 (ContentElementFrame
                                        (@0ContentElementFrame
                                          (@0SomeContentElement (rp_content R1)))
                                        (@1ContentElementFrame
                                          (@0SomeContentElement (rp_content R1)))))
                                 (a!4 (frame_src (@0ContentElementFrame
                                                   (@0SomeContentElement
                                                     (rp_content R1)))))
                                 (a!6 (ContentElementScript
                                        (@0ContentElementScript
                                          (@0SomeContentElement (rp_content R1)))))
                                 (a!7 (script_src (@0ContentElementScript
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                 (a!9 (ContentElementImage
                                        (@0ContentElementImage
                                          (@0SomeContentElement (rp_content R1)))))
                                 (a!10 (image_src (@0ContentElementImage
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                 (a!13 (= (rp_content R1)
                                          (SomeContentElement
                                            (@0SomeContentElement
                                              (rp_content R1)))))
                                 (a!14 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeScript
                                            ContentTypeHTML))
                                 (a!18 (SomeContentType (@0SomeContentType
                                                          (rp_hd_content_type
                                                            (rp_headers R1)))))
                                 (a!21 (and (= (url_protocol (rp_url R1))
                                               ProtocolBlob)
                                            (= (rp_hd_csp (rp_headers R1))
                                               NoneCSP)))
                                 (a!22 (and (= (url_protocol (rp_url R1))
                                               ProtocolData)
                                            (= (rp_hd_csp (rp_headers R1))
                                               NoneCSP)))
                                 (a!24 (html_body (@0ContentElementHTML
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                 (a!46 (@0ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!47 (@1ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!48 (@2ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!49 (@3ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!50 (@4ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!51 (@defaultArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                 (a!58 (= (rp_hd_csp (dc_headers (wd_document S1)))
                                          NoneCSP))
                                 (a!59 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document S1)))))
                                 (a!63 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location S1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location S1)))))
                                 (a!64 (SomeOrigin (TupleOrigin (url_protocol (wd_location S1))
                                                                (url_host (wd_location S1))
                                                                (url_port (wd_location S1)))))
                                 (a!65 (OpaqueOrigin (@0url_path_data (url_path (wd_location S1)))))
                                 (a!67 (SomeOrigin (@0url_path_blob (url_path (wd_location S1)))))
                                 (a!110 (script_nonce (@0ContentElementScript
                                                        (@0SomeContentElement
                                                          (rp_content R1)))))
                                 (a!112 (@0ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!113 (@1ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!114 (@2ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!115 (@3ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!116 (@4ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!117 (@defaultArrayoptionInt
                                          (in_body (dc_init (wd_document S1)))))
                                 (a!121 (= (rp_hd_csp (rp_headers R1))
                                           (rp_hd_csp (dc_headers (wd_document O1)))))
                                 (a!129 (url_path_data (@0url_path_data (url_path (rp_url R1)))
                                                       (@1url_path_data (url_path (rp_url R1)))))
                                 (a!131 (url_path_res (@0url_path_res (url_path (rp_url R1)))))
                                 (a!133 (= (@1url_path_blob (url_path (rp_url R1)))
                                           0))
                                 (a!134 (= (@1url_path_blob (url_path (rp_url R1)))
                                           1))
                                 (a!135 (= (@1url_path_blob (url_path (rp_url R1)))
                                           2))
                                 (a!136 (= (@1url_path_blob (url_path (rp_url R1)))
                                           3))
                                 (a!137 (= (@1url_path_blob (url_path (rp_url R1)))
                                           4))
                                 (a!142 (url_path_blob (@0url_path_blob (url_path (rp_url R1)))
                                                       (@1url_path_blob (url_path (rp_url R1)))))
                                 (a!148 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content R1)))))
                                 (a!151 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content R1)))))
                                 (a!175 (SomeDOMElement (DOMElementResource
                                                          (rp_url R1)
                                                          (@0SomeContentElement
                                                            (rp_content R1)))))
                                 (a!176 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!177 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!178 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!179 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!180 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!181 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!189 (= (ft_emitter N1)
                                           (EmitterForm (@0EmitterForm (ft_emitter N1))
                                                        (@1EmitterForm (ft_emitter N1)))))
                                 (a!190 (= (ft_emitter N1)
                                           (EmitterScript (@0EmitterScript (ft_emitter N1))
                                                          (@1EmitterScript (ft_emitter N1)))))
                                 (a!192 (and (= (rp_hd_location (rp_headers R1))
                                                NoneURL)
                                             (= (rp_code R1) ResponseFound)))
                                 (a!193 (and (= (rp_hd_location (rp_headers R1))
                                                NoneURL)
                                             (= (rp_code R1)
                                                ResponseTemporaryRedirect)))
                                 (a!194 (ite (= M1 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= M1 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!197 (not (= (rp_hd_content_type
                                                  (rp_headers R1))
                                                NoneContentType)))
                                 (a!199 (ContentElementHTML
                                          (@0ContentElementHTML
                                            (@0SomeContentElement
                                              (rp_content V)))))
                                 (a!200 (ContentElementFrame
                                          (@0ContentElementFrame
                                            (@0SomeContentElement
                                              (rp_content V)))
                                          (@1ContentElementFrame
                                            (@0SomeContentElement
                                              (rp_content V)))))
                                 (a!201 (frame_src (@0ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!203 (ContentElementScript
                                          (@0ContentElementScript
                                            (@0SomeContentElement
                                              (rp_content V)))))
                                 (a!204 (script_src (@0ContentElementScript
                                                      (@0SomeContentElement
                                                        (rp_content V)))))
                                 (a!206 (ContentElementImage
                                          (@0ContentElementImage
                                            (@0SomeContentElement
                                              (rp_content V)))))
                                 (a!207 (image_src (@0ContentElementImage
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!210 (= (rp_content V)
                                           (SomeContentElement
                                             (@0SomeContentElement
                                               (rp_content V)))))
                                 (a!211 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeScript
                                             ContentTypeHTML))
                                 (a!215 (SomeContentType (@0SomeContentType
                                                           (rp_hd_content_type
                                                             (rp_headers V)))))
                                 (a!218 (and (= (url_protocol (rp_url V))
                                                ProtocolBlob)
                                             (= (rp_hd_csp (rp_headers V))
                                                NoneCSP)))
                                 (a!219 (and (= (url_protocol (rp_url V))
                                                ProtocolData)
                                             (= (rp_hd_csp (rp_headers V))
                                                NoneCSP)))
                                 (a!221 (html_body (@0ContentElementHTML
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!243 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!244 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!245 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!246 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!247 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!248 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!255 (= (rp_hd_csp (dc_headers (wd_document W)))
                                           NoneCSP))
                                 (a!256 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document W)))))
                                 (a!289 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location W)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location W)))))
                                 (a!290 (SomeOrigin (TupleOrigin (url_protocol (wd_location W))
                                                                 (url_host (wd_location W))
                                                                 (url_port (wd_location W)))))
                                 (a!291 (OpaqueOrigin (@0url_path_data (url_path (wd_location W)))))
                                 (a!293 (SomeOrigin (@0url_path_blob (url_path (wd_location W)))))
                                 (a!307 (script_nonce (@0ContentElementScript
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!309 (@0ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!310 (@1ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!311 (@2ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!312 (@3ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!313 (@4ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!314 (@defaultArrayoptionInt
                                          (in_body (dc_init (wd_document W)))))
                                 (a!318 (= (rp_hd_csp (rp_headers V))
                                           (rp_hd_csp (dc_headers (wd_document S)))))
                                 (a!326 (url_path_data (@0url_path_data (url_path (rp_url V)))
                                                       (@1url_path_data (url_path (rp_url V)))))
                                 (a!328 (url_path_res (@0url_path_res (url_path (rp_url V)))))
                                 (a!330 (= (@1url_path_blob (url_path (rp_url V)))
                                           0))
                                 (a!331 (= (@1url_path_blob (url_path (rp_url V)))
                                           1))
                                 (a!332 (= (@1url_path_blob (url_path (rp_url V)))
                                           2))
                                 (a!333 (= (@1url_path_blob (url_path (rp_url V)))
                                           3))
                                 (a!334 (= (@1url_path_blob (url_path (rp_url V)))
                                           4))
                                 (a!339 (url_path_blob (@0url_path_blob (url_path (rp_url V)))
                                                       (@1url_path_blob (url_path (rp_url V)))))
                                 (a!345 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!348 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!372 (SomeDOMElement (DOMElementResource
                                                          (rp_url V)
                                                          (@0SomeContentElement
                                                            (rp_content V)))))
                                 (a!373 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!374 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!375 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!376 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!377 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!378 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!386 (= (ft_emitter R)
                                           (EmitterForm (@0EmitterForm (ft_emitter R))
                                                        (@1EmitterForm (ft_emitter R)))))
                                 (a!387 (= (ft_emitter R)
                                           (EmitterScript (@0EmitterScript (ft_emitter R))
                                                          (@1EmitterScript (ft_emitter R)))))
                                 (a!389 (and (= (rp_hd_location (rp_headers V))
                                                NoneURL)
                                             (= (rp_code V) ResponseFound)))
                                 (a!390 (and (= (rp_hd_location (rp_headers V))
                                                NoneURL)
                                             (= (rp_code V)
                                                ResponseTemporaryRedirect)))
                                 (a!391 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!392 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!393 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!394 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!395 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!396 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!403 (DOMElementResource
                                          (rp_url C1)
                                          (ContentElementFrame
                                            (Build_Frame (frame_src D1) E1)
                                            F1)))
                                 (a!409 (ite (= E1 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= E1 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!412 (ite (= Q 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= Q 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!415 (ite (= (frame_window D1) 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!418 (not (= (rp_hd_content_type
                                                  (rp_headers V))
                                                NoneContentType)))
                                 (a!420 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url I1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url I1)))))
                                 (a!421 (SomeOrigin (TupleOrigin (url_protocol (rp_url I1))
                                                                 (url_host (rp_url I1))
                                                                 (url_port (rp_url I1)))))
                                 (a!422 (OpaqueOrigin (@0url_path_data (url_path (rp_url I1)))))
                                 (a!424 (SomeOrigin (@0url_path_blob (url_path (rp_url I1)))))
                                 (a!428 (ite (= D 3)
                                             (@3ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 4)
                                                  (@4ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  (@defaultArrayprodOriginoptionCSP
                                                    (origin_csp X1)))))
                                 (a!433 (or (and (= U1 DOMTopLevel)
                                                 (= F2
                                                    (Build_ArrayoptionBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob
                                                      NoneBlob)))
                                            (and (= U1 (DOMIndex V1)) (= F2 W1)))))
                           (let ((a!5 (and (= (@0SomeContentElement
                                                (rp_content R1))
                                              a!3)
                                           (= a!4 (rp_url R1))))
                                 (a!8 (and (= (@0SomeContentElement
                                                (rp_content R1))
                                              a!6)
                                           (= a!7 (rp_url R1))))
                                 (a!11 (and (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!9)
                                            (= a!10 (rp_url R1))))
                                 (a!15 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeImage
                                            a!14))
                                 (a!23 (or (= (url_protocol (rp_url R1))
                                              ProtocolHTTPS)
                                           (= (url_protocol (rp_url R1))
                                              ProtocolHTTP)
                                           a!21
                                           a!22))
                                 (a!25 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!24)))))
                                 (a!26 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!28 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!24)))))
                                 (a!29 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!31 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!24)))))
                                 (a!32 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!34 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!24)))))
                                 (a!35 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!37 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!24)))))
                                 (a!38 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!40 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!24)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!24)))))
                                 (a!41 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!24)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!24)))))
                                 (a!52 (ite (= (@0DOMIndex Q1) 3)
                                            a!49
                                            (ite (= (@0DOMIndex Q1) 4)
                                                 a!50
                                                 a!51)))
                                 (a!60 (= (url_protocol a!7)
                                          (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!61 (CSPSrcScheme (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!66 (ite ((_ is url_path_data)
                                              (url_path (wd_location S1)))
                                            (SomeOrigin a!65)
                                            NoneOrigin))
                                 (a!68 (ite ((_ is url_path_blob)
                                              (url_path (wd_location S1)))
                                            a!67
                                            NoneOrigin))
                                 (a!71 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!7)))))
                                 (a!72 (ite ((_ is url_path_blob)
                                              (url_path a!7))
                                            (SomeOrigin (@0url_path_blob (url_path a!7)))
                                            NoneOrigin))
                                 (a!77 (= (url_host a!7)
                                          (SomeDomain (@0SomeDomain (url_host a!7)))))
                                 (a!78 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!79 (subdomain (@0subdomain (@0SomeDomain (url_host a!7)))
                                                  (@1subdomain (@0SomeDomain (url_host a!7)))))
                                 (a!84 (domain (@0domain (@0SomeDomain (url_host a!7)))))
                                 (a!85 (= (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          NoneoptionInt))
                                 (a!87 (= (@0domain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!89 (= (@1subdomain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!91 (= (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          NoneProtocol))
                                 (a!92 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!95 (= (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          NoneInt))
                                 (a!96 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!99 (= (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          NonePath))
                                 (a!100 (= (url_path a!7)
                                           (url_path_res (@0url_path_res (url_path a!7)))))
                                 (a!101 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!104 (CSPSrcSource (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                                      (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                                      (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                                      (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                                      (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!107 (= (csp_script_src a!59)
                                           (SomeCSPSrc (@0SomeCSPSrc (csp_script_src a!59)))))
                                 (a!108 (= (rp_hd_csp (dc_headers (wd_document S1)))
                                           (SomeCSP a!59)))
                                 (a!118 (ite (= (@0DOMIndex Q1) 3)
                                             a!115
                                             (ite (= (@0DOMIndex Q1) 4)
                                                  a!116
                                                  a!117)))
                                 (a!122 (and (not (c_csp_inherit_local_from_initiator
                                                    (config L1)))
                                             a!121))
                                 (a!138 (ite a!135
                                             (@2ArrayoptionBlob K1)
                                             (ite a!136
                                                  (@3ArrayoptionBlob K1)
                                                  (ite a!137
                                                       (@4ArrayoptionBlob K1)
                                                       (@defaultArrayoptionBlob
                                                         K1)))))
                                 (a!149 (ite (= a!148 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= a!148 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!152 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!151)))))
                                 (a!153 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!155 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!151)))))
                                 (a!156 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!158 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!151)))))
                                 (a!159 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!161 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!151)))))
                                 (a!162 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!164 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!151)))))
                                 (a!165 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!167 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!151)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!151)))))
                                 (a!168 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!151)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!151)))))
                                 (a!182 (ite (= (@0DOMIndex Q1) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!181
                                               a!176
                                               a!177
                                               a!178
                                               a!175
                                               a!180)
                                             (dm_body (dc_dom (wd_document S1)))))
                                 (a!191 (or (and a!189 (= Q1 DOMTopLevel))
                                            (and a!190 (not (= Q1 DOMTopLevel)))
                                            (= (ft_emitter N1) EmitterClient)))
                                 (a!195 (ite (= M1 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= M1 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!194)))
                                 (a!202 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!200)
                                             (= a!201 (rp_url V))))
                                 (a!205 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!203)
                                             (= a!204 (rp_url V))))
                                 (a!208 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!206)
                                             (= a!207 (rp_url V))))
                                 (a!212 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeImage
                                             a!211))
                                 (a!220 (or (= (url_protocol (rp_url V))
                                               ProtocolHTTPS)
                                            (= (url_protocol (rp_url V))
                                               ProtocolHTTP)
                                            a!218
                                            a!219))
                                 (a!222 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!221)))))
                                 (a!223 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!225 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!221)))))
                                 (a!226 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!228 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!221)))))
                                 (a!229 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!231 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!221)))))
                                 (a!232 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!234 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!221)))))
                                 (a!235 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!237 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!221)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!221)))))
                                 (a!238 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!221)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!221)))))
                                 (a!249 (ite (= (@0DOMIndex U) 3)
                                             a!246
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!247
                                                  a!248)))
                                 (a!257 (= (url_host a!204)
                                           (SomeDomain (@0SomeDomain (url_host a!204)))))
                                 (a!258 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!259 (subdomain (@0subdomain (@0SomeDomain (url_host a!204)))
                                                   (@1subdomain (@0SomeDomain (url_host a!204)))))
                                 (a!264 (domain (@0domain (@0SomeDomain (url_host a!204)))))
                                 (a!265 (= (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           NoneoptionInt))
                                 (a!267 (= (@0domain (@0SomeDomain (url_host a!204)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!269 (= (@1subdomain (@0SomeDomain (url_host a!204)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!271 (= (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           NoneProtocol))
                                 (a!272 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!275 (= (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           NoneInt))
                                 (a!276 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!279 (= (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           NonePath))
                                 (a!280 (= (url_path a!204)
                                           (url_path_res (@0url_path_res (url_path a!204)))))
                                 (a!281 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!284 (CSPSrcSource (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                                      (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                                      (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                                      (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                                      (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!286 (= (url_protocol a!204)
                                           (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!287 (CSPSrcScheme (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!292 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             (SomeOrigin a!291)
                                             NoneOrigin))
                                 (a!294 (ite ((_ is url_path_blob)
                                               (url_path (wd_location W)))
                                             a!293
                                             NoneOrigin))
                                 (a!297 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!204)))))
                                 (a!298 (ite ((_ is url_path_blob)
                                               (url_path a!204))
                                             (SomeOrigin (@0url_path_blob (url_path a!204)))
                                             NoneOrigin))
                                 (a!304 (= (csp_script_src a!256)
                                           (SomeCSPSrc (@0SomeCSPSrc (csp_script_src a!256)))))
                                 (a!305 (= (rp_hd_csp (dc_headers (wd_document W)))
                                           (SomeCSP a!256)))
                                 (a!315 (ite (= (@0DOMIndex U) 3)
                                             a!312
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!313
                                                  a!314)))
                                 (a!319 (and (not (c_csp_inherit_local_from_initiator
                                                    (config P)))
                                             a!318))
                                 (a!335 (ite a!332
                                             (@2ArrayoptionBlob O)
                                             (ite a!333
                                                  (@3ArrayoptionBlob O)
                                                  (ite a!334
                                                       (@4ArrayoptionBlob O)
                                                       (@defaultArrayoptionBlob
                                                         O)))))
                                 (a!346 (ite (= a!345 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!345 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!349 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!348)))))
                                 (a!350 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!352 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!348)))))
                                 (a!353 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!355 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!348)))))
                                 (a!356 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!358 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!348)))))
                                 (a!359 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!361 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!348)))))
                                 (a!362 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!364 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!348)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!348)))))
                                 (a!365 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!348)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!348)))))
                                 (a!379 (ite (= (@0DOMIndex U) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!378
                                               a!373
                                               a!374
                                               a!375
                                               a!372
                                               a!377)
                                             (dm_body (dc_dom (wd_document W)))))
                                 (a!388 (or (and a!386 (= U DOMTopLevel))
                                            (and a!387 (not (= U DOMTopLevel)))
                                            (= (ft_emitter R) EmitterClient)))
                                 (a!397 (ite (= B1 2)
                                             a!393
                                             (ite (= B1 3)
                                                  a!394
                                                  (ite (= B1 4) a!395 a!396))))
                                 (a!404 (ite (= B1 4)
                                             (Build_ArrayoptionDOMElement
                                               a!391
                                               a!392
                                               a!393
                                               a!394
                                               (SomeDOMElement a!403)
                                               a!396)
                                             (dm_body (dc_dom (wd_document G1)))))
                                 (a!410 (ite (= E1 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= E1 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!409)))
                                 (a!413 (ite (= Q 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= Q 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!412)))
                                 (a!416 (ite (= (frame_window D1) 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!415)))
                                 (a!423 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             (SomeOrigin a!422)
                                             NoneOrigin))
                                 (a!425 (ite ((_ is url_path_blob)
                                               (url_path (rp_url I1)))
                                             a!424
                                             NoneOrigin))
                                 (a!429 (ite (= D 1)
                                             (@1ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 2)
                                                  (@2ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  a!428))))
                           (let ((a!12 (or (= (@0SomeContentElement
                                                (rp_content R1))
                                              a!2)
                                           a!5
                                           a!8
                                           a!11))
                                 (a!16 (ite ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ContentTypeHTML
                                            a!15))
                                 (a!27 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!24)))
                                            (SomeDOMElement (DOMElementForm a!26))
                                            NoneDOMElement))
                                 (a!30 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!24)))
                                            (SomeDOMElement (DOMElementForm a!29))
                                            NoneDOMElement))
                                 (a!33 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!24)))
                                            (SomeDOMElement (DOMElementForm a!32))
                                            NoneDOMElement))
                                 (a!36 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!24)))
                                            (SomeDOMElement (DOMElementForm a!35))
                                            NoneDOMElement))
                                 (a!39 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!24)))
                                            (SomeDOMElement (DOMElementForm a!38))
                                            NoneDOMElement))
                                 (a!42 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!24)))
                                            (SomeDOMElement (DOMElementForm a!41))
                                            NoneDOMElement))
                                 (a!53 (ite (= (@0DOMIndex Q1) 1)
                                            a!47
                                            (ite (= (@0DOMIndex Q1) 2)
                                                 a!48
                                                 a!52)))
                                 (a!62 (and a!60
                                            (= (@0SomeCSPSrc (csp_script_src a!59))
                                               a!61)))
                                 (a!69 (ite ((_ is url_path_data)
                                              (url_path (wd_location S1)))
                                            NoneOrigin
                                            a!68))
                                 (a!73 (ite ((_ is ProtocolData)
                                              (url_protocol a!7))
                                            (ite ((_ is url_path_data)
                                                   (url_path a!7))
                                                 a!71
                                                 NoneOrigin)
                                            (ite ((_ is url_path_data)
                                                   (url_path a!7))
                                                 NoneOrigin
                                                 a!72)))
                                 (a!80 (and a!77
                                            (= a!78 NoneInt)
                                            (= (@0SomeDomain (url_host a!7))
                                               a!79)))
                                 (a!81 (= (@0subdomain (@0SomeDomain (url_host a!7)))
                                          (@0SomeInt a!78)))
                                 (a!83 (= (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          (SomeoptionInt a!78)))
                                 (a!86 (and a!77
                                            (= (@0SomeDomain (url_host a!7))
                                               a!84)
                                            a!85))
                                 (a!88 (and a!87
                                            (= (@0SomeDomain (url_host a!7))
                                               a!84)))
                                 (a!90 (and a!89
                                            (= (@0SomeDomain (url_host a!7))
                                               a!79)))
                                 (a!93 (= (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          (SomeProtocol a!92)))
                                 (a!97 (= (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                          (SomeInt a!96)))
                                 (a!102 (= (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!59)))
                                           (SomePath a!101)))
                                 (a!119 (ite (= (@0DOMIndex Q1) 1)
                                             a!113
                                             (ite (= (@0DOMIndex Q1) 2)
                                                  a!114
                                                  a!118)))
                                 (a!139 (@0SomeBlob (ite a!133
                                                         (@0ArrayoptionBlob K1)
                                                         (ite a!134
                                                              (@1ArrayoptionBlob
                                                                K1)
                                                              a!138))))
                                 (a!150 (ite (= a!148 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= a!148 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!149)))
                                 (a!154 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!153))
                                             NoneDOMElement))
                                 (a!157 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!156))
                                             NoneDOMElement))
                                 (a!160 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!159))
                                             NoneDOMElement))
                                 (a!163 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!162))
                                             NoneDOMElement))
                                 (a!166 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!165))
                                             NoneDOMElement))
                                 (a!169 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!151)))
                                             (SomeDOMElement (DOMElementForm a!168))
                                             NoneDOMElement))
                                 (a!183 (ite (= (@0DOMIndex Q1) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!181
                                               a!176
                                               a!175
                                               a!178
                                               a!179
                                               a!180)
                                             (ite (= (@0DOMIndex Q1) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!181
                                                    a!176
                                                    a!177
                                                    a!175
                                                    a!179
                                                    a!180)
                                                  a!182)))
                                 (a!196 (= (ite (= M1 0)
                                                (@0ArrayWindow (windows L1))
                                                a!195)
                                           O1))
                                 (a!209 (or (= (@0SomeContentElement
                                                 (rp_content V))
                                               a!199)
                                            a!202
                                            a!205
                                            a!208))
                                 (a!213 (ite ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeHTML
                                             a!212))
                                 (a!224 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!223))
                                             NoneDOMElement))
                                 (a!227 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!226))
                                             NoneDOMElement))
                                 (a!230 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!229))
                                             NoneDOMElement))
                                 (a!233 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!232))
                                             NoneDOMElement))
                                 (a!236 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!235))
                                             NoneDOMElement))
                                 (a!239 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!221)))
                                             (SomeDOMElement (DOMElementForm a!238))
                                             NoneDOMElement))
                                 (a!250 (ite (= (@0DOMIndex U) 1)
                                             a!244
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!245
                                                  a!249)))
                                 (a!260 (and a!257
                                             (= a!258 NoneInt)
                                             (= (@0SomeDomain (url_host a!204))
                                                a!259)))
                                 (a!261 (= (@0subdomain (@0SomeDomain (url_host a!204)))
                                           (@0SomeInt a!258)))
                                 (a!263 (= (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           (SomeoptionInt a!258)))
                                 (a!266 (and a!257
                                             (= (@0SomeDomain (url_host a!204))
                                                a!264)
                                             a!265))
                                 (a!268 (and a!267
                                             (= (@0SomeDomain (url_host a!204))
                                                a!264)))
                                 (a!270 (and a!269
                                             (= (@0SomeDomain (url_host a!204))
                                                a!259)))
                                 (a!273 (= (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           (SomeProtocol a!272)))
                                 (a!277 (= (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           (SomeInt a!276)))
                                 (a!282 (= (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!256)))
                                           (SomePath a!281)))
                                 (a!288 (and a!286
                                             (= (@0SomeCSPSrc (csp_script_src a!256))
                                                a!287)))
                                 (a!295 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             NoneOrigin
                                             a!294))
                                 (a!299 (ite ((_ is ProtocolData)
                                               (url_protocol a!204))
                                             (ite ((_ is url_path_data)
                                                    (url_path a!204))
                                                  a!297
                                                  NoneOrigin)
                                             (ite ((_ is url_path_data)
                                                    (url_path a!204))
                                                  NoneOrigin
                                                  a!298)))
                                 (a!316 (ite (= (@0DOMIndex U) 1)
                                             a!310
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!311
                                                  a!315)))
                                 (a!336 (@0SomeBlob (ite a!330
                                                         (@0ArrayoptionBlob O)
                                                         (ite a!331
                                                              (@1ArrayoptionBlob
                                                                O)
                                                              a!335))))
                                 (a!347 (ite (= a!345 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!345 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!346)))
                                 (a!351 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!350))
                                             NoneDOMElement))
                                 (a!354 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!353))
                                             NoneDOMElement))
                                 (a!357 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!356))
                                             NoneDOMElement))
                                 (a!360 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!359))
                                             NoneDOMElement))
                                 (a!363 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!362))
                                             NoneDOMElement))
                                 (a!366 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!348)))
                                             (SomeDOMElement (DOMElementForm a!365))
                                             NoneDOMElement))
                                 (a!380 (ite (= (@0DOMIndex U) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!378
                                               a!373
                                               a!372
                                               a!375
                                               a!376
                                               a!377)
                                             (ite (= (@0DOMIndex U) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!378
                                                    a!373
                                                    a!374
                                                    a!372
                                                    a!376
                                                    a!377)
                                                  a!379)))
                                 (a!398 (ite (= B1 0)
                                             a!391
                                             (ite (= B1 1) a!392 a!397)))
                                 (a!405 (ite (= B1 2)
                                             (Build_ArrayoptionDOMElement
                                               a!391
                                               a!392
                                               (SomeDOMElement a!403)
                                               a!394
                                               a!395
                                               a!396)
                                             (ite (= B1 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!391
                                                    a!392
                                                    a!393
                                                    (SomeDOMElement a!403)
                                                    a!395
                                                    a!396)
                                                  a!404)))
                                 (a!411 (= (ite (= E1 0)
                                                (@0ArrayWindow (windows X))
                                                a!410)
                                           Y))
                                 (a!414 (= (ite (= Q 0)
                                                (@0ArrayWindow (windows P))
                                                a!413)
                                           S))
                                 (a!417 (= (ite (= (frame_window D1) 0)
                                                (@0ArrayWindow (windows X))
                                                a!416)
                                           I))
                                 (a!426 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             NoneOrigin
                                             a!425))
                                 (a!430 (= (ite (= D 0)
                                                (@0ArrayprodOriginoptionCSP
                                                  (origin_csp X1))
                                                a!429)
                                           (pairOriginoptionCSP E G))))
                           (let ((a!17 (= a!16
                                          (@0SomeContentType
                                            (rp_hd_content_type (rp_headers R1)))))
                                 (a!43 (Build_ArrayoptionDOMElement
                                         (ite ((_ is SomeHTMLElement)
                                                (@0ArrayoptionHTMLElement a!24))
                                              (ite a!25 NoneDOMElement a!27)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@1ArrayoptionHTMLElement a!24))
                                              (ite a!28 NoneDOMElement a!30)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@2ArrayoptionHTMLElement a!24))
                                              (ite a!31 NoneDOMElement a!33)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@3ArrayoptionHTMLElement a!24))
                                              (ite a!34 NoneDOMElement a!36)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@4ArrayoptionHTMLElement a!24))
                                              (ite a!37 NoneDOMElement a!39)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@defaultArrayoptionHTMLElement
                                                  a!24))
                                              (ite a!40 NoneDOMElement a!42)
                                              NoneDOMElement)))
                                 (a!54 (@0SomeHTMLElement
                                         (ite (= (@0DOMIndex Q1) 0) a!46 a!53)))
                                 (a!70 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location S1)))
                                            a!66
                                            a!69))
                                 (a!74 (ite (or ((_ is ProtocolHTTPS)
                                                  (url_protocol a!7))
                                                ((_ is ProtocolHTTP)
                                                  (url_protocol a!7)))
                                            (SomeOrigin (TupleOrigin (url_protocol a!7)
                                                                     (url_host a!7)
                                                                     (url_port a!7)))
                                            a!73))
                                 (a!82 (and a!81
                                            a!77
                                            (= a!78 (SomeInt (@0SomeInt a!78)))
                                            (= (@0SomeDomain (url_host a!7))
                                               a!79)))
                                 (a!94 (or a!91
                                           (and (= (url_protocol a!7) a!92)
                                                a!93)))
                                 (a!98 (or a!95
                                           (and a!97
                                                (= (url_port a!7)
                                                   (SomeInt a!96)))))
                                 (a!103 (and a!100
                                             (= (@0url_path_res (url_path a!7))
                                                a!101)
                                             a!102))
                                 (a!120 (= (ite (= (@0DOMIndex Q1) 0)
                                                a!112
                                                a!119)
                                           NoneInt))
                                 (a!123 (@0SomeInt (ite (= (@0DOMIndex Q1) 0)
                                                        a!112
                                                        a!119)))
                                 (a!140 (and (c_csp_inherit_blob_from_creator
                                               (config L1))
                                             (= (rp_hd_csp (rp_headers R1))
                                                (blob_csp a!139))))
                                 (a!143 (= (ite a!133
                                                (@0ArrayoptionBlob K1)
                                                (ite a!134
                                                     (@1ArrayoptionBlob K1)
                                                     a!138))
                                           (SomeBlob a!139)))
                                 (a!170 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!152 NoneDOMElement a!154)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!155 NoneDOMElement a!157)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!158 NoneDOMElement a!160)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!161 NoneDOMElement a!163)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!164 NoneDOMElement a!166)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!151))
                                               (ite a!167 NoneDOMElement a!169)
                                               NoneDOMElement)))
                                 (a!184 (ite (= (@0DOMIndex Q1) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!175
                                               a!176
                                               a!177
                                               a!178
                                               a!179
                                               a!180)
                                             (ite (= (@0DOMIndex Q1) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!181
                                                    a!175
                                                    a!177
                                                    a!178
                                                    a!179
                                                    a!180)
                                                  a!183)))
                                 (a!214 (= a!213
                                           (@0SomeContentType
                                             (rp_hd_content_type (rp_headers V)))))
                                 (a!240 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!222 NoneDOMElement a!224)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!225 NoneDOMElement a!227)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!228 NoneDOMElement a!230)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!231 NoneDOMElement a!233)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!234 NoneDOMElement a!236)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!221))
                                               (ite a!237 NoneDOMElement a!239)
                                               NoneDOMElement)))
                                 (a!251 (@0SomeHTMLElement
                                          (ite (= (@0DOMIndex U) 0) a!243 a!250)))
                                 (a!262 (and a!261
                                             a!257
                                             (= a!258
                                                (SomeInt (@0SomeInt a!258)))
                                             (= (@0SomeDomain (url_host a!204))
                                                a!259)))
                                 (a!274 (or a!271
                                            (and (= (url_protocol a!204) a!272)
                                                 a!273)))
                                 (a!278 (or a!275
                                            (and a!277
                                                 (= (url_port a!204)
                                                    (SomeInt a!276)))))
                                 (a!283 (and a!280
                                             (= (@0url_path_res (url_path a!204))
                                                a!281)
                                             a!282))
                                 (a!296 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location W)))
                                             a!292
                                             a!295))
                                 (a!300 (ite (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!204))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!204)))
                                             (SomeOrigin (TupleOrigin (url_protocol a!204)
                                                                      (url_host a!204)
                                                                      (url_port a!204)))
                                             a!299))
                                 (a!317 (= (ite (= (@0DOMIndex U) 0)
                                                a!309
                                                a!316)
                                           NoneInt))
                                 (a!320 (@0SomeInt (ite (= (@0DOMIndex U) 0)
                                                        a!309
                                                        a!316)))
                                 (a!337 (and (c_csp_inherit_blob_from_creator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (blob_csp a!336))))
                                 (a!340 (= (ite a!330
                                                (@0ArrayoptionBlob O)
                                                (ite a!331
                                                     (@1ArrayoptionBlob O)
                                                     a!335))
                                           (SomeBlob a!336)))
                                 (a!367 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!349 NoneDOMElement a!351)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!352 NoneDOMElement a!354)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!355 NoneDOMElement a!357)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!358 NoneDOMElement a!360)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!361 NoneDOMElement a!363)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!348))
                                               (ite a!364 NoneDOMElement a!366)
                                               NoneDOMElement)))
                                 (a!381 (ite (= (@0DOMIndex U) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!372
                                               a!373
                                               a!374
                                               a!375
                                               a!376
                                               a!377)
                                             (ite (= (@0DOMIndex U) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!378
                                                    a!372
                                                    a!374
                                                    a!375
                                                    a!376
                                                    a!377)
                                                  a!380)))
                                 (a!399 (= (@0SomeDOMElement a!398)
                                           (DOMElementResource
                                             (@0DOMElementResource
                                               (@0SomeDOMElement a!398))
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!398)))))
                                 (a!400 (ContentElementFrame
                                          (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!398)))
                                          (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!398)))))
                                 (a!401 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!398)))
                                           D1))
                                 (a!402 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!398)))
                                           F1))
                                 (a!406 (ite (= B1 0)
                                             (Build_ArrayoptionDOMElement
                                               (SomeDOMElement a!403)
                                               a!392
                                               a!393
                                               a!394
                                               a!395
                                               a!396)
                                             (ite (= B1 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!391
                                                    (SomeDOMElement a!403)
                                                    a!393
                                                    a!394
                                                    a!395
                                                    a!396)
                                                  a!405)))
                                 (a!427 (ite ((_ is ProtocolData)
                                               (url_protocol (rp_url I1)))
                                             a!423
                                             a!426)))
                           (let ((a!19 (and (or (= (rp_content R1)
                                                   NoneContentElement)
                                                (and a!12 a!13 a!17))
                                            (= (rp_hd_content_type
                                                 (rp_headers R1))
                                               a!18)))
                                 (a!44 (Build_Document (+ 1 P1)
                                                       (ft_correlator N1)
                                                       (rp_headers R1)
                                                       (@0ContentElementHTML
                                                         (@0SomeContentElement
                                                           (rp_content R1)))
                                                       (Build_DOM (ft_correlator N1)
                                                                  0
                                                                  a!43)
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!55 (and (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!9)
                                            (= a!54 (HTMLImage a!10))))
                                 (a!56 (and (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!6)
                                            (= a!54 (HTMLScript a!7))))
                                 (a!57 (and (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!3)
                                            (= a!54 (HTMLFrame a!4))))
                                 (a!75 (= (SomeOrigin (@0SomeOrigin (ite a!63
                                                                         a!64
                                                                         a!70)))
                                          a!74))
                                 (a!105 (and (or (and (or a!80 a!82) a!83) a!86)
                                             (or a!88 a!90)
                                             a!94
                                             a!98
                                             (or a!99 a!103)
                                             a!77
                                             (= (@0SomeCSPSrc (csp_script_src a!59))
                                                a!104)))
                                 (a!106 (= (ite a!63 a!64 a!70)
                                           (SomeOrigin (@0SomeOrigin (ite a!63
                                                                          a!64
                                                                          a!70)))))
                                 (a!124 (ite (= a!123 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= a!123 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!128 (= (ite (= (@0DOMIndex Q1) 0)
                                                a!112
                                                a!119)
                                           (SomeInt a!123)))
                                 (a!171 (Build_Document (+ 1 P1)
                                                        (ft_correlator N1)
                                                        (rp_headers R1)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content R1)))
                                                        (Build_DOM (ft_correlator N1)
                                                                   0
                                                                   a!170)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!185 (Build_DOM (dm_nonce (dc_dom (wd_document S1)))
                                                   (dm_head (dc_dom (wd_document S1)))
                                                   a!184))
                                 (a!187 (= (ite (= (@0DOMIndex Q1) 0) a!46 a!53)
                                           (SomeHTMLElement a!54)))
                                 (a!216 (and (or (= (rp_content V)
                                                    NoneContentElement)
                                                 (and a!209 a!210 a!214))
                                             (= (rp_hd_content_type
                                                  (rp_headers V))
                                                a!215)))
                                 (a!241 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@0ContentElementHTML
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!240)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!252 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!206)
                                             (= a!251 (HTMLImage a!207))))
                                 (a!253 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!203)
                                             (= a!251 (HTMLScript a!204))))
                                 (a!254 (and (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!200)
                                             (= a!251 (HTMLFrame a!201))))
                                 (a!285 (and (or (and (or a!260 a!262) a!263)
                                                 a!266)
                                             (or a!268 a!270)
                                             a!274
                                             a!278
                                             (or a!279 a!283)
                                             a!257
                                             (= (@0SomeCSPSrc (csp_script_src a!256))
                                                a!284)))
                                 (a!301 (= (SomeOrigin (@0SomeOrigin (ite a!289
                                                                          a!290
                                                                          a!296)))
                                           a!300))
                                 (a!303 (= (ite a!289 a!290 a!296)
                                           (SomeOrigin (@0SomeOrigin (ite a!289
                                                                          a!290
                                                                          a!296)))))
                                 (a!321 (ite (= a!320 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!320 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!325 (= (ite (= (@0DOMIndex U) 0)
                                                a!309
                                                a!316)
                                           (SomeInt a!320)))
                                 (a!368 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!367)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!382 (Build_DOM (dm_nonce (dc_dom (wd_document W)))
                                                   (dm_head (dc_dom (wd_document W)))
                                                   a!381))
                                 (a!384 (= (ite (= (@0DOMIndex U) 0)
                                                a!243
                                                a!250)
                                           (SomeHTMLElement a!251)))
                                 (a!407 (Build_DOM (dm_nonce (dc_dom (wd_document G1)))
                                                   (dm_head (dc_dom (wd_document G1)))
                                                   a!406))
                                 (a!431 (and (c_origin_wide_csp (config X1))
                                             (= (ite a!420 a!421 a!427)
                                                (SomeOrigin F))
                                             a!430
                                             (= E F)
                                             (= (rp_hd_csp (rp_headers I1)) G))))
                           (let ((a!20 (or (= (rp_hd_content_type
                                                (rp_headers R1))
                                              NoneContentType)
                                           a!19))
                                 (a!45 (and a!23
                                            (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!2)
                                            (= O1
                                               (Build_Window (ft_correlator N1)
                                                             NoneInt
                                                             (rp_url R1)
                                                             NoneDomain
                                                             a!44))
                                            (= Q1 DOMTopLevel)))
                                 (a!76 (and a!75
                                            (= (@0SomeCSPSrc (csp_script_src a!59))
                                               CSPSrcSelf)))
                                 (a!125 (ite (= a!123 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= a!123 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!124)))
                                 (a!172 (= (ite (= a!148 0)
                                                (@0ArrayWindow (windows L1))
                                                a!150)
                                           (Build_Window (ft_correlator N1)
                                                         (SomeInt M1)
                                                         (rp_url R1)
                                                         NoneDomain
                                                         a!171)))
                                 (a!186 (Build_Window (wd_nonce S1)
                                                      (wd_parent S1)
                                                      (wd_location S1)
                                                      (wd_document_domain S1)
                                                      (Build_Document (+ 1 P1)
                                                                      (dc_nonce (wd_document S1))
                                                                      (dc_headers (wd_document S1))
                                                                      (dc_html (wd_document S1))
                                                                      a!185
                                                                      (dc_init (wd_document S1)))))
                                 (a!217 (or (= (rp_hd_content_type
                                                 (rp_headers V))
                                               NoneContentType)
                                            a!216))
                                 (a!242 (and a!220
                                             (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!199)
                                             (= S
                                                (Build_Window (ft_correlator R)
                                                              NoneInt
                                                              (rp_url V)
                                                              NoneDomain
                                                              a!241))
                                             (= U DOMTopLevel)))
                                 (a!302 (and a!301
                                             (= (@0SomeCSPSrc (csp_script_src a!256))
                                                CSPSrcSelf)))
                                 (a!322 (ite (= a!320 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!320 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!321)))
                                 (a!369 (= (ite (= a!345 0)
                                                (@0ArrayWindow (windows P))
                                                a!347)
                                           (Build_Window (ft_correlator R)
                                                         (SomeInt Q)
                                                         (rp_url V)
                                                         NoneDomain
                                                         a!368)))
                                 (a!383 (Build_Window (wd_nonce W)
                                                      (wd_parent W)
                                                      (wd_location W)
                                                      (wd_document_domain W)
                                                      (Build_Document (+ 1 T)
                                                                      (dc_nonce (wd_document W))
                                                                      (dc_headers (wd_document W))
                                                                      (dc_html (wd_document W))
                                                                      a!382
                                                                      (dc_init (wd_document W)))))
                                 (a!408 (Build_Window (wd_nonce G1)
                                                      (wd_parent G1)
                                                      (wd_location G1)
                                                      (wd_document_domain G1)
                                                      (Build_Document (+ 1 A1)
                                                                      (dc_nonce (wd_document G1))
                                                                      (dc_headers (wd_document G1))
                                                                      (dc_html (wd_document G1))
                                                                      a!407
                                                                      (dc_init (wd_document G1)))))
                                 (a!432 (or (not (c_origin_wide_csp (config X1)))
                                            a!431)))
                           (let ((a!109 (and (or (= (csp_script_src a!59)
                                                    NoneCSPSrc)
                                                 (and (or a!62 a!76 a!105)
                                                      a!106
                                                      a!107))
                                             a!108))
                                 (a!126 (wd_document (ite (= a!123 0)
                                                          (@0ArrayWindow (windows L1))
                                                          a!125)))
                                 (a!306 (and (or (= (csp_script_src a!256)
                                                    NoneCSPSrc)
                                                 (and (or a!285 a!288 a!302)
                                                      a!303
                                                      a!304))
                                             a!305))
                                 (a!323 (wd_document (ite (= a!320 0)
                                                          (@0ArrayWindow (windows P))
                                                          a!322))))
                           (let ((a!111 (and (or a!58 a!109)
                                             (= a!110 P1)
                                             (= (@0SomeContentElement
                                                  (rp_content R1))
                                                a!6)))
                                 (a!127 (and (c_csp_inherit_local_from_initiator
                                               (config L1))
                                             (= (rp_hd_csp (rp_headers R1))
                                                (rp_hd_csp (dc_headers a!126)))))
                                 (a!308 (and (or a!255 a!306)
                                             (= a!307 T)
                                             (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!203)))
                                 (a!324 (and (c_csp_inherit_local_from_initiator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (rp_hd_csp (dc_headers a!323))))))
                           (let ((a!130 (and (or (and a!120 a!121)
                                                 (and (or a!122 a!127) a!128))
                                             (= (url_path (rp_url R1)) a!129)))
                                 (a!132 (and (or (and a!120 a!121)
                                                 (and (or a!122 a!127) a!128))
                                             (= (url_path (rp_url R1)) a!131)))
                                 (a!141 (and (or (and a!120 a!121)
                                                 (and (or a!122 a!127) a!128))
                                             (not (c_csp_inherit_blob_from_creator
                                                    (config L1)))))
                                 (a!327 (and (or (and a!317 a!318)
                                                 (and (or a!319 a!324) a!325))
                                             (= (url_path (rp_url V)) a!326)))
                                 (a!329 (and (or (and a!317 a!318)
                                                 (and (or a!319 a!324) a!325))
                                             (= (url_path (rp_url V)) a!328)))
                                 (a!338 (and (or (and a!317 a!318)
                                                 (and (or a!319 a!324) a!325))
                                             (not (c_csp_inherit_blob_from_creator
                                                    (config P))))))
                           (let ((a!144 (and (or a!140 a!141)
                                             (= (url_path (rp_url R1)) a!142)
                                             a!143))
                                 (a!341 (and (or a!337 a!338)
                                             (= (url_path (rp_url V)) a!339)
                                             a!340)))
                           (let ((a!145 (and (or a!130 a!132 a!144)
                                             (= (url_protocol (rp_url R1))
                                                ProtocolData)))
                                 (a!146 (and (or a!130 a!132 a!144)
                                             (= (url_protocol (rp_url R1))
                                                ProtocolBlob)))
                                 (a!342 (and (or a!327 a!329 a!341)
                                             (= (url_protocol (rp_url V))
                                                ProtocolData)))
                                 (a!343 (and (or a!327 a!329 a!341)
                                             (= (url_protocol (rp_url V))
                                                ProtocolBlob))))
                           (let ((a!147 (or (= (url_protocol (rp_url R1))
                                               ProtocolHTTPS)
                                            (= (url_protocol (rp_url R1))
                                               ProtocolHTTP)
                                            a!145
                                            a!146))
                                 (a!344 (or (= (url_protocol (rp_url V))
                                               ProtocolHTTPS)
                                            (= (url_protocol (rp_url V))
                                               ProtocolHTTP)
                                            a!342
                                            a!343)))
                           (let ((a!173 (and a!147
                                             (= (@0SomeContentElement
                                                  (rp_content R1))
                                                a!3)
                                             a!172))
                                 (a!370 (and a!344
                                             (= (@0SomeContentElement
                                                  (rp_content V))
                                                a!200)
                                             a!369)))
                           (let ((a!174 (or (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!9)
                                            (= (@0SomeContentElement
                                                 (rp_content R1))
                                               a!2)
                                            a!111
                                            a!173))
                                 (a!371 (or (= (@0SomeContentElement
                                                 (rp_content V))
                                               a!206)
                                            (= (@0SomeContentElement
                                                 (rp_content V))
                                               a!199)
                                            a!308
                                            a!370)))
                           (let ((a!188 (and (or a!55 a!56 a!57)
                                             a!174
                                             (= O1 a!186)
                                             (= Q1 (DOMIndex (@0DOMIndex Q1)))
                                             a!187))
                                 (a!385 (and (or a!252 a!253 a!254)
                                             a!371
                                             (= S a!383)
                                             (= U (DOMIndex (@0DOMIndex U)))
                                             a!384)))
                           (let ((a!198 (and a!20
                                             (or a!45 a!188)
                                             a!191
                                             (or (= (rp_code R1) ResponseOk)
                                                 a!192
                                                 a!193)
                                             (= A2 P1)
                                             (= D2 O1)
                                             (= H1 S1)
                                             a!196
                                             (= Y1 J1)
                                             (= J1 (DOMPath nilInt Q1))
                                             (= (ft_response N1)
                                                (SomeResponse R1))
                                             (= X1 L1)
                                             (= (rp_code R1) ResponseOk)
                                             (= B2 N1)
                                             a!13
                                             (= I1 R1)
                                             a!197
                                             (= W1 K1)))
                                 (a!419 (and a!217
                                             (or a!242 a!385)
                                             a!388
                                             (or (= (rp_code V) ResponseOk)
                                                 a!389
                                                 a!390)
                                             (= A2 A1)
                                             (= A1 T)
                                             (= a!398
                                                (SomeDOMElement (@0SomeDOMElement a!398)))
                                             a!399
                                             (= (@1DOMElementResource
                                                  (@0SomeDOMElement a!398))
                                                a!400)
                                             a!401
                                             a!402
                                             (= D2 Z)
                                             (= H1 G1)
                                             (= Y S)
                                             (= Z a!408)
                                             (= I W)
                                             a!411
                                             a!414
                                             a!417
                                             (= Y1 H)
                                             (= N (DOMPath J K))
                                             (= N (DOMPath nilInt U))
                                             (= H (DOMPath (consInt B1 J) K))
                                             (= (ft_response R)
                                                (SomeResponse V))
                                             (= X1 X)
                                             (= X P)
                                             (= (rp_code V) ResponseOk)
                                             (= B2 M)
                                             (= M R)
                                             a!210
                                             (= I1 C1)
                                             (= C1 V)
                                             a!418
                                             (= W1 L)
                                             (= L O))))
                           (let ((a!434 (and (Reachable X1 Z1 A)
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
                                             (or a!198 a!419)
                                             a!432
                                             a!433
                                             (= C
                                                (consEvent (EvDOMUpdate Y1) Z1)))))
                             (=> a!434 (Reachable X1 C B)))))))))))))))))))
                           :weight 0))))
      (a!90 (asserted (forall ((A State)
                               (B State)
                               (C listEvent)
                               (D Script)
                               (E NestedDOMPath)
                               (F NestedDOMPath)
                               (G Int)
                               (H Window)
                               (I HTML)
                               (J Frame)
                               (K listInt)
                               (L DOMSelector)
                               (M Window)
                               (N Window)
                               (O Global)
                               (P Global)
                               (Q NestedDOMPath)
                               (R DOMSelector)
                               (S Window)
                               (T Window)
                               (U Window)
                               (V Global)
                               (W Global)
                               (X NestedDOMPath)
                               (Y DOMSelector)
                               (Z Window)
                               (A1 Window)
                               (B1 NestedDOMPath)
                               (C1 listInt)
                               (D1 Int)
                               (E1 Window)
                               (F1 Script)
                               (G1 Form)
                               (H1 NestedDOMPath)
                               (I1 NestedDOMPath)
                               (J1 Int)
                               (K1 Window)
                               (L1 HTML)
                               (M1 Frame)
                               (N1 listInt)
                               (O1 DOMSelector)
                               (P1 Window)
                               (Q1 Window)
                               (R1 Global)
                               (S1 Global)
                               (T1 NestedDOMPath)
                               (U1 DOMSelector)
                               (V1 Window)
                               (W1 Window)
                               (X1 Window)
                               (Y1 Global)
                               (Z1 Global)
                               (A2 NestedDOMPath)
                               (B2 DOMSelector)
                               (C2 Window)
                               (D2 Window)
                               (E2 NestedDOMPath)
                               (F2 listInt)
                               (G2 Int)
                               (H2 Window)
                               (I2 Form)
                               (J2 Emitter)
                               (K2 Request)
                               (L2 Int)
                               (M2 Window)
                               (N2 Script)
                               (O2 NestedDOMPath)
                               (P2 Window)
                               (Q2 Global)
                               (R2 NestedDOMPath)
                               (S2 Int)
                               (T2 Window)
                               (U2 HTML)
                               (V2 Frame)
                               (W2 listInt)
                               (X2 DOMSelector)
                               (Y2 Window)
                               (Z2 Window)
                               (A3 Global)
                               (B3 Global)
                               (C3 NestedDOMPath)
                               (D3 DOMSelector)
                               (E3 Window)
                               (F3 Window)
                               (G3 Window)
                               (H3 Global)
                               (I3 Global)
                               (J3 NestedDOMPath)
                               (K3 DOMSelector)
                               (L3 Window)
                               (M3 Window)
                               (N3 NestedDOMPath)
                               (O3 listInt)
                               (P3 Int)
                               (Q3 Window)
                               (R3 Script)
                               (S3 Int)
                               (T3 Int)
                               (U3 Int)
                               (V3 Origin)
                               (W3 Blob)
                               (X3 Int)
                               (Y3 Int)
                               (Z3 Int)
                               (A4 Origin)
                               (B4 Blob)
                               (C4 Int)
                               (D4 Int)
                               (E4 FetchEngine)
                               (F4 Int)
                               (G4 SetCookie)
                               (H4 ArrayoptionSetCookie)
                               (I4 ArrayoptionSetCookie)
                               (J4 Response)
                               (K4 Int)
                               (L4 listEvent)
                               (M4 Int)
                               (N4 FetchEngine)
                               (O4 ServiceWorker)
                               (P4 ArrayoptionSetCookie)
                               (Q4 ArrayoptionBlob)
                               (R4 ArrayoptionStorageItem))
                        (! (let ((a!1 (ite (= D4 3)
                                           (@3ArrayResponse (responses Q2))
                                           (ite (= D4 4)
                                                (@4ArrayResponse (responses Q2))
                                                (@defaultArrayResponse
                                                  (responses Q2)))))
                                 (a!4 (SomeprodprodEmitterIntInt
                                        (pairprodEmitterIntInt
                                          (pairEmitterInt (ft_emitter E4) C4)
                                          D4)))
                                 (a!10 (ite (= C4 3)
                                            (@3ArrayRequest (requests Q2))
                                            (ite (= C4 4)
                                                 (@4ArrayRequest (requests Q2))
                                                 (@defaultArrayRequest
                                                   (requests Q2)))))
                                 (a!13 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!14 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!15 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!16 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!17 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!18 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!25 (ite (= (frame_window M1) 3)
                                            (@3ArrayWindow (windows R1))
                                            (ite (= (frame_window M1) 4)
                                                 (@4ArrayWindow (windows R1))
                                                 (@defaultArrayWindow
                                                   (windows R1)))))
                                 (a!30 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!31 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!32 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!33 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!34 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!35 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!40 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!41 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!42 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!43 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!44 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!45 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!52 (ite (= (frame_window J) 3)
                                            (@3ArrayWindow (windows O))
                                            (ite (= (frame_window J) 4)
                                                 (@4ArrayWindow (windows O))
                                                 (@defaultArrayWindow
                                                   (windows O)))))
                                 (a!57 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!58 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!59 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!60 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!61 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!62 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document E1)))))
                                 (a!69 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!70 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!71 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!72 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!73 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!74 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document T2)))))
                                 (a!81 (ite (= (frame_window V2) 3)
                                            (@3ArrayWindow (windows A3))
                                            (ite (= (frame_window V2) 4)
                                                 (@4ArrayWindow (windows A3))
                                                 (@defaultArrayWindow
                                                   (windows A3)))))
                                 (a!86 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!87 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!88 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!89 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!90 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!91 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q3)))))
                                 (a!97 (ite (= L2 3)
                                            (@3ArrayEmitter (emitters Q2))
                                            (ite (= L2 4)
                                                 (@4ArrayEmitter (emitters Q2))
                                                 (@defaultArrayEmitter
                                                   (emitters Q2)))))
                                 (a!102 (ite (= C4 3)
                                             (@3ArrayInt (server_responses Q2))
                                             (ite (= C4 4)
                                                  (@4ArrayInt (server_responses Q2))
                                                  (@defaultArrayInt (server_responses Q2)))))
                                 (a!114 (ite (= X3 3)
                                             (@3ArrayContentElement
                                               (data_urls Q2))
                                             (ite (= X3 4)
                                                  (@4ArrayContentElement
                                                    (data_urls Q2))
                                                  (@defaultArrayContentElement
                                                    (data_urls Q2)))))
                                 (a!118 (ite (= Z3 2)
                                             (@2ArrayoptionBlob Q4)
                                             (ite (= Z3 3)
                                                  (@3ArrayoptionBlob Q4)
                                                  (ite (= Z3 4)
                                                       (@4ArrayoptionBlob Q4)
                                                       (@defaultArrayoptionBlob
                                                         Q4)))))
                                 (a!122 (ite (= S3 3)
                                             (@3ArrayContentElement
                                               (data_urls Q2))
                                             (ite (= S3 4)
                                                  (@4ArrayContentElement
                                                    (data_urls Q2))
                                                  (@defaultArrayContentElement
                                                    (data_urls Q2)))))
                                 (a!126 (ite (= U3 2)
                                             (@2ArrayoptionBlob Q4)
                                             (ite (= U3 3)
                                                  (@3ArrayoptionBlob Q4)
                                                  (ite (= U3 4)
                                                       (@4ArrayoptionBlob Q4)
                                                       (@defaultArrayoptionBlob
                                                         Q4)))))
                                 (a!130 (and (= (rp_hd_set_cookie (rp_headers J4))
                                                NoneSetCookie)
                                             (= P4 I4)))
                                 (a!131 (and (sc_secure G4)
                                             (= (url_protocol (rp_url J4))
                                                ProtocolHTTPS)
                                             (= (sc_same_site G4) SSNone)))
                                 (a!132 (= (sc_domain G4)
                                           (SomeDomain (@0SomeDomain (sc_domain G4)))))
                                 (a!133 (@0domain (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!135 ((_ is domain)
                                          (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!137 (@0subdomain (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!139 (@1subdomain (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!142 (or (not (sc_secure G4))
                                            (= (url_protocol (rp_url J4))
                                               ProtocolHTTPS)))
                                 (a!143 (SomeDomain (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!144 (= (sc_reg_domain G4)
                                           (@0SomeDomain (url_host (rp_url J4)))))
                                 (a!145 (= (sc_name G4)
                                           (NoPrefix (@0NoPrefix (sc_name G4)))))
                                 (a!147 (= (sc_name G4)
                                           (Secure (@0Secure (sc_name G4)))))
                                 (a!149 (url_path_res (@0url_path_res (url_path (rp_url J4)))))
                                 (a!150 (= (sc_name G4)
                                           (Host (@0Host (sc_name G4)))))
                                 (a!151 (= (@0url_path_res (url_path (rp_url J4)))
                                           slash))
                                 (a!153 (ite (= F4 2)
                                             (@2ArrayoptionSetCookie H4)
                                             (ite (= F4 3)
                                                  (@3ArrayoptionSetCookie H4)
                                                  (ite (= F4 4)
                                                       (@4ArrayoptionSetCookie
                                                         H4)
                                                       (@defaultArrayoptionSetCookie
                                                         H4)))))
                                 (a!155 (ite (= F4 3)
                                             (Build_ArrayoptionSetCookie
                                               (@0ArrayoptionSetCookie H4)
                                               (@1ArrayoptionSetCookie H4)
                                               (@2ArrayoptionSetCookie H4)
                                               (SomeSetCookie G4)
                                               (@4ArrayoptionSetCookie H4)
                                               (@defaultArrayoptionSetCookie H4))
                                             (ite (= F4 4)
                                                  (Build_ArrayoptionSetCookie
                                                    (@0ArrayoptionSetCookie H4)
                                                    (@1ArrayoptionSetCookie H4)
                                                    (@2ArrayoptionSetCookie H4)
                                                    (@3ArrayoptionSetCookie H4)
                                                    (SomeSetCookie G4)
                                                    (@defaultArrayoptionSetCookie
                                                      H4))
                                                  H4)))
                                 (a!158 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!159 (= (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!160 (= (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!162 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!163 (= (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!164 (= (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!166 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!167 (= (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!168 (= (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!170 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!171 (= (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!172 (= (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!174 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!175 (= (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!176 (= (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!178 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             I4)))
                                           (sc_reg_domain G4)))
                                 (a!179 (= (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       I4)))
                                           (sc_name G4)))
                                 (a!180 (= (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       I4)))
                                           (sc_path G4)))
                                 (a!184 (SomeOrigin (@0SomeOrigin (rp_hd_access_control_allow_origin
                                                                    (rp_headers J4)))))
                                 (a!185 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location M2)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location M2)))))
                                 (a!186 (SomeOrigin (TupleOrigin (url_protocol (wd_location M2))
                                                                 (url_host (wd_location M2))
                                                                 (url_port (wd_location M2)))))
                                 (a!187 (OpaqueOrigin (@0url_path_data (url_path (wd_location M2)))))
                                 (a!189 (SomeOrigin (@0url_path_blob (url_path (wd_location M2)))))
                                 (a!193 (= (ft_emitter E4)
                                           (EmitterCORSPreflight
                                             (@0EmitterCORSPreflight
                                               (ft_emitter E4))
                                             (@1EmitterCORSPreflight
                                               (ft_emitter E4)))))
                                 (a!194 (= (ft_emitter E4)
                                           (EmitterScript (@0EmitterScript (ft_emitter E4))
                                                          (@1EmitterScript (ft_emitter E4)))))
                                 (a!196 (= (ft_emitter E4)
                                           (EmitterForm (@0EmitterForm (ft_emitter E4))
                                                        (@1EmitterForm (ft_emitter E4))))))
                           (let ((a!2 (ite (= D4 1)
                                           (@1ArrayResponse (responses Q2))
                                           (ite (= D4 2)
                                                (@2ArrayResponse (responses Q2))
                                                a!1)))
                                 (a!5 (ite (= K4 4)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             a!4
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E4)))
                                           (ft_history E4)))
                                 (a!11 (ite (= C4 1)
                                            (@1ArrayRequest (requests Q2))
                                            (ite (= C4 2)
                                                 (@2ArrayRequest (requests Q2))
                                                 a!10)))
                                 (a!19 (ite (= J1 2)
                                            a!15
                                            (ite (= J1 3)
                                                 a!16
                                                 (ite (= J1 4) a!17 a!18))))
                                 (a!26 (ite (= (frame_window M1) 1)
                                            (@1ArrayWindow (windows R1))
                                            (ite (= (frame_window M1) 2)
                                                 (@2ArrayWindow (windows R1))
                                                 a!25)))
                                 (a!36 (ite (= G2 2)
                                            a!32
                                            (ite (= G2 3)
                                                 a!33
                                                 (ite (= G2 4) a!34 a!35))))
                                 (a!46 (ite (= G 2)
                                            a!42
                                            (ite (= G 3)
                                                 a!43
                                                 (ite (= G 4) a!44 a!45))))
                                 (a!53 (ite (= (frame_window J) 1)
                                            (@1ArrayWindow (windows O))
                                            (ite (= (frame_window J) 2)
                                                 (@2ArrayWindow (windows O))
                                                 a!52)))
                                 (a!63 (ite (= D1 2)
                                            a!59
                                            (ite (= D1 3)
                                                 a!60
                                                 (ite (= D1 4) a!61 a!62))))
                                 (a!75 (ite (= S2 2)
                                            a!71
                                            (ite (= S2 3)
                                                 a!72
                                                 (ite (= S2 4) a!73 a!74))))
                                 (a!82 (ite (= (frame_window V2) 1)
                                            (@1ArrayWindow (windows A3))
                                            (ite (= (frame_window V2) 2)
                                                 (@2ArrayWindow (windows A3))
                                                 a!81)))
                                 (a!92 (ite (= P3 2)
                                            a!88
                                            (ite (= P3 3)
                                                 a!89
                                                 (ite (= P3 4) a!90 a!91))))
                                 (a!98 (ite (= L2 1)
                                            (@1ArrayEmitter (emitters Q2))
                                            (ite (= L2 2)
                                                 (@2ArrayEmitter (emitters Q2))
                                                 a!97)))
                                 (a!103 (ite (= C4 1)
                                             (@1ArrayInt (server_responses Q2))
                                             (ite (= C4 2)
                                                  (@2ArrayInt (server_responses Q2))
                                                  a!102)))
                                 (a!115 (ite (= X3 1)
                                             (@1ArrayContentElement
                                               (data_urls Q2))
                                             (ite (= X3 2)
                                                  (@2ArrayContentElement
                                                    (data_urls Q2))
                                                  a!114)))
                                 (a!119 (= (ite (= Z3 0)
                                                (@0ArrayoptionBlob Q4)
                                                (ite (= Z3 1)
                                                     (@1ArrayoptionBlob Q4)
                                                     a!118))
                                           (SomeBlob B4)))
                                 (a!123 (ite (= S3 1)
                                             (@1ArrayContentElement
                                               (data_urls Q2))
                                             (ite (= S3 2)
                                                  (@2ArrayContentElement
                                                    (data_urls Q2))
                                                  a!122)))
                                 (a!127 (= (ite (= U3 0)
                                                (@0ArrayoptionBlob Q4)
                                                (ite (= U3 1)
                                                     (@1ArrayoptionBlob Q4)
                                                     a!126))
                                           (SomeBlob W3)))
                                 (a!134 (= (@0domain (@0SomeDomain (sc_domain G4)))
                                           a!133))
                                 (a!136 (= (@1subdomain (@0SomeDomain (sc_domain G4)))
                                           a!133))
                                 (a!138 (= (@0subdomain (@0SomeDomain (sc_domain G4)))
                                           a!137))
                                 (a!140 (= (@1subdomain (@0SomeDomain (sc_domain G4)))
                                           a!139))
                                 (a!152 (and a!142
                                             (sc_secure G4)
                                             (= (url_path (rp_url J4)) a!149)
                                             (= (url_host (rp_url J4)) a!143)
                                             (= (sc_domain G4) NoneDomain)
                                             a!144
                                             a!150
                                             a!151
                                             (= (sc_path G4) slash)))
                                 (a!154 (= (ite (= F4 0)
                                                (@0ArrayoptionSetCookie H4)
                                                (ite (= F4 1)
                                                     (@1ArrayoptionSetCookie H4)
                                                     a!153))
                                           NoneSetCookie))
                                 (a!156 (ite (= F4 1)
                                             (Build_ArrayoptionSetCookie
                                               (@0ArrayoptionSetCookie H4)
                                               (SomeSetCookie G4)
                                               (@2ArrayoptionSetCookie H4)
                                               (@3ArrayoptionSetCookie H4)
                                               (@4ArrayoptionSetCookie H4)
                                               (@defaultArrayoptionSetCookie H4))
                                             (ite (= F4 2)
                                                  (Build_ArrayoptionSetCookie
                                                    (@0ArrayoptionSetCookie H4)
                                                    (@1ArrayoptionSetCookie H4)
                                                    (SomeSetCookie G4)
                                                    (@3ArrayoptionSetCookie H4)
                                                    (@4ArrayoptionSetCookie H4)
                                                    (@defaultArrayoptionSetCookie
                                                      H4))
                                                  a!155)))
                                 (a!161 (ite (and a!158 a!159 a!160)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                               I4)))))
                                 (a!165 (ite (and a!162 a!163 a!164)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                               I4)))))
                                 (a!169 (ite (and a!166 a!167 a!168)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                               I4)))))
                                 (a!173 (ite (and a!170 a!171 a!172)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                               I4)))))
                                 (a!177 (ite (and a!174 a!175 a!176)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                               I4)))))
                                 (a!181 (ite (and a!178 a!179 a!180)
                                             NoneSetCookie
                                             (SomeSetCookie (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                               I4)))))
                                 (a!188 (ite ((_ is url_path_data)
                                               (url_path (wd_location M2)))
                                             (SomeOrigin a!187)
                                             NoneOrigin))
                                 (a!190 (ite ((_ is url_path_blob)
                                               (url_path (wd_location M2)))
                                             a!189
                                             NoneOrigin)))
                           (let ((a!3 (= J4
                                         (ite (= D4 0)
                                              (@0ArrayResponse (responses Q2))
                                              a!2)))
                                 (a!6 (ite (= K4 3)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             a!4
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E4)))
                                           a!5))
                                 (a!12 (= (ft_request E4)
                                          (ite (= C4 0)
                                               (@0ArrayRequest (requests Q2))
                                               a!11)))
                                 (a!20 (ite (= J1 0)
                                            a!13
                                            (ite (= J1 1) a!14 a!19)))
                                 (a!27 (= (ite (= (frame_window M1) 0)
                                               (@0ArrayWindow (windows R1))
                                               a!26)
                                          P1))
                                 (a!37 (ite (= G2 0)
                                            a!30
                                            (ite (= G2 1) a!31 a!36)))
                                 (a!47 (ite (= G 0)
                                            a!40
                                            (ite (= G 1) a!41 a!46)))
                                 (a!54 (= (ite (= (frame_window J) 0)
                                               (@0ArrayWindow (windows O))
                                               a!53)
                                          M))
                                 (a!64 (ite (= D1 0)
                                            a!57
                                            (ite (= D1 1) a!58 a!63)))
                                 (a!76 (ite (= S2 0)
                                            a!69
                                            (ite (= S2 1) a!70 a!75)))
                                 (a!83 (= (ite (= (frame_window V2) 0)
                                               (@0ArrayWindow (windows A3))
                                               a!82)
                                          Y2))
                                 (a!93 (ite (= P3 0)
                                            a!86
                                            (ite (= P3 1) a!87 a!92)))
                                 (a!99 (= (ite (= L2 0)
                                               (@0ArrayEmitter (emitters Q2))
                                               a!98)
                                          (EmitterScript O2 N2)))
                                 (a!101 (rq_url (ite (= C4 0)
                                                     (@0ArrayRequest (requests Q2))
                                                     a!11)))
                                 (a!104 (= (ite (= C4 0)
                                                (@0ArrayInt (server_responses Q2))
                                                a!103)
                                           0))
                                 (a!105 (= (ite (= C4 0)
                                                (@0ArrayInt (server_responses Q2))
                                                a!103)
                                           1))
                                 (a!106 (= (ite (= C4 0)
                                                (@0ArrayInt (server_responses Q2))
                                                a!103)
                                           2))
                                 (a!107 (= (ite (= C4 0)
                                                (@0ArrayInt (server_responses Q2))
                                                a!103)
                                           3))
                                 (a!108 (= (ite (= C4 0)
                                                (@0ArrayInt (server_responses Q2))
                                                a!103)
                                           4))
                                 (a!116 (SomeContentElement
                                          (ite (= X3 0)
                                               (@0ArrayContentElement
                                                 (data_urls Q2))
                                               a!115)))
                                 (a!120 (and (= (url_path (rp_url J4))
                                                (url_path_blob A4 Z3))
                                             (= (blob_origin B4) A4)
                                             (= (rp_url J4) (blob_url B4))
                                             a!119
                                             (= (rp_content J4)
                                                (SomeContentElement
                                                  (blob_celt B4)))))
                                 (a!124 (SomeContentElement
                                          (ite (= S3 0)
                                               (@0ArrayContentElement
                                                 (data_urls Q2))
                                               a!123)))
                                 (a!128 (and (= (url_path (rp_url J4))
                                                (url_path_blob V3 U3))
                                             (= (blob_origin W3) V3)
                                             (= (rp_url J4) (blob_url W3))
                                             a!127
                                             (= (rp_content J4)
                                                (SomeContentElement
                                                  (blob_celt W3)))))
                                 (a!141 (ite ((_ is domain)
                                               (@0SomeDomain (sc_domain G4)))
                                             (and a!134 a!135)
                                             (ite a!135 a!136 (and a!138 a!140))))
                                 (a!157 (= P4
                                           (ite (= F4 0)
                                                (Build_ArrayoptionSetCookie
                                                  (SomeSetCookie G4)
                                                  (@1ArrayoptionSetCookie H4)
                                                  (@2ArrayoptionSetCookie H4)
                                                  (@3ArrayoptionSetCookie H4)
                                                  (@4ArrayoptionSetCookie H4)
                                                  (@defaultArrayoptionSetCookie
                                                    H4))
                                                a!156)))
                                 (a!182 (Build_ArrayoptionSetCookie
                                          (ite ((_ is SomeSetCookie)
                                                 (@0ArrayoptionSetCookie I4))
                                               a!161
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@1ArrayoptionSetCookie I4))
                                               a!165
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@2ArrayoptionSetCookie I4))
                                               a!169
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@3ArrayoptionSetCookie I4))
                                               a!173
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@4ArrayoptionSetCookie I4))
                                               a!177
                                               NoneSetCookie)
                                          (ite ((_ is SomeSetCookie)
                                                 (@defaultArrayoptionSetCookie
                                                   I4))
                                               a!181
                                               NoneSetCookie)))
                                 (a!191 (ite ((_ is url_path_data)
                                               (url_path (wd_location M2)))
                                             NoneOrigin
                                             a!190)))
                           (let ((a!7 (ite (= K4 2)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             a!4
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E4)))
                                           a!6))
                                 (a!21 (= (@0SomeDOMElement a!20)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!20))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!20)))))
                                 (a!22 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!20)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!20)))))
                                 (a!23 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!20)))
                                          M1))
                                 (a!24 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!20)))
                                          L1))
                                 (a!38 (= (@0SomeDOMElement a!37)
                                          (DOMElementForm (@0DOMElementForm (@0SomeDOMElement a!37)))))
                                 (a!48 (= (@0SomeDOMElement a!47)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!47))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!47)))))
                                 (a!49 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!47)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!47)))))
                                 (a!50 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!47)))
                                          J))
                                 (a!51 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!47)))
                                          I))
                                 (a!65 (= (@0SomeDOMElement a!64)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!64))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!64)))))
                                 (a!66 (ContentElementScript
                                         (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!64)))))
                                 (a!67 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!64)))
                                          F1))
                                 (a!77 (= (@0SomeDOMElement a!76)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!76))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!76)))))
                                 (a!78 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!76)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!76)))))
                                 (a!79 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!76)))
                                          V2))
                                 (a!80 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!76)))
                                          U2))
                                 (a!94 (= (@0SomeDOMElement a!93)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!93))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!93)))))
                                 (a!95 (ContentElementScript
                                         (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!93)))))
                                 (a!96 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!93)))
                                          R3))
                                 (a!109 (ite a!107
                                             (@3ArrayResponse (responses Q2))
                                             (ite a!108
                                                  (@4ArrayResponse (responses Q2))
                                                  (@defaultArrayResponse
                                                    (responses Q2)))))
                                 (a!117 (and (= Y3 M4)
                                             (= (url_path (rp_url J4))
                                                (url_path_data Y3 X3))
                                             (= (rp_content J4) a!116)))
                                 (a!125 (and (= T3 M4)
                                             (= (url_path (rp_url J4))
                                                (url_path_data T3 S3))
                                             (= (rp_content J4) a!124)))
                                 (a!146 (and (or (= (sc_domain G4) NoneDomain)
                                                 (and a!132 a!141))
                                             a!142
                                             (= (url_host (rp_url J4)) a!143)
                                             a!144
                                             a!145))
                                 (a!148 (and (or (= (sc_domain G4) NoneDomain)
                                                 (and a!132 a!141))
                                             a!142
                                             (sc_secure G4)
                                             (= (url_host (rp_url J4)) a!143)
                                             a!144
                                             a!147))
                                 (a!192 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location M2)))
                                             a!188
                                             a!191)))
                           (let ((a!8 (ite (= K4 1)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             a!4
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E4)))
                                           a!7))
                                 (a!28 (and (= a!20
                                               (SomeDOMElement (@0SomeDOMElement a!20)))
                                            a!21
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!20))
                                               a!22)
                                            a!23
                                            a!24
                                            (= X1 K1)
                                            (= P1 W1)
                                            (= H2 Q1)
                                            (= V1 W1)
                                            (= Q1 V1)
                                            a!27
                                            (= I1 (DOMPath (consInt J1 N1) O1))
                                            (= T1 (DOMPath N1 O1))
                                            (= T1 (DOMPath nilInt U1))
                                            (= E2 I1)
                                            (= R1 S1)
                                            (= Y1 R1)))
                                 (a!55 (and (= a!47
                                               (SomeDOMElement (@0SomeDOMElement a!47)))
                                            a!48
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!47))
                                               a!49)
                                            a!50
                                            a!51
                                            (= U H)
                                            (= M T)
                                            (= E1 N)
                                            (= S T)
                                            (= N S)
                                            a!54
                                            (= B1 F)
                                            (= Q (DOMPath K L))
                                            (= Q (DOMPath nilInt R))
                                            (= F (DOMPath (consInt G K) L))
                                            (= V O)
                                            (= O P)))
                                 (a!84 (and (= a!76
                                               (SomeDOMElement (@0SomeDOMElement a!76)))
                                            a!77
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!76))
                                               a!78)
                                            a!79
                                            a!80
                                            (= G3 T2)
                                            (= Q3 Z2)
                                            (= Y2 F3)
                                            (= Z2 E3)
                                            (= E3 F3)
                                            a!83
                                            (= N3 R2)
                                            (= C3 (DOMPath W2 X2))
                                            (= C3 (DOMPath nilInt D3))
                                            (= R2 (DOMPath (consInt S2 W2) X2))
                                            (= A3 B3)
                                            (= H3 A3)))
                                 (a!110 (ite a!105
                                             (@1ArrayResponse (responses Q2))
                                             (ite a!106
                                                  (@2ArrayResponse (responses Q2))
                                                  a!109)))
                                 (a!121 (and (or a!117 a!120)
                                             (= (rp_hd_access_control_allow_origin
                                                  (rp_headers J4))
                                                NoneOrigin)
                                             (= (url_protocol (rp_url J4))
                                                ProtocolBlob)
                                             (= (rp_hd_location (rp_headers J4))
                                                NoneURL)
                                             (= (rp_code J4) ResponseOk)
                                             (= (rp_hd_set_cookie (rp_headers J4))
                                                NoneSetCookie)))
                                 (a!129 (and (or a!125 a!128)
                                             (= (rp_hd_access_control_allow_origin
                                                  (rp_headers J4))
                                                NoneOrigin)
                                             (= (url_protocol (rp_url J4))
                                                ProtocolData)
                                             (= (rp_hd_location (rp_headers J4))
                                                NoneURL)
                                             (= (rp_code J4) ResponseOk)
                                             (= (rp_hd_set_cookie (rp_headers J4))
                                                NoneSetCookie)))
                                 (a!183 (and (or (= (sc_same_site G4) SSLax)
                                                 (= (sc_same_site G4) SSStrict)
                                                 a!131)
                                             (or a!146 a!148 a!152)
                                             (= (rp_hd_set_cookie (rp_headers J4))
                                                (SomeSetCookie G4))
                                             a!154
                                             a!157
                                             (= H4 a!182)))
                                 (a!195 (and (or (= (rp_content J4)
                                                    NoneContentElement)
                                                 (= a!184
                                                    (ite a!185 a!186 a!192)))
                                             a!194)))
                           (let ((a!9 (ite (= K4 0)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             a!4
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E4))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E4)))
                                           a!8))
                                 (a!29 (or (and (= X1 D2)
                                                (= C2 D2)
                                                (= H2 C2)
                                                (= A2 (DOMPath nilInt B2))
                                                (= E2 A2)
                                                (= Y1 Z1))
                                           a!28))
                                 (a!56 (or (and (= U A1)
                                                (= Z A1)
                                                (= E1 Z)
                                                (= X (DOMPath nilInt Y))
                                                (= B1 X)
                                                (= V W))
                                           a!55))
                                 (a!85 (or (and (= G3 M3)
                                                (= Q3 L3)
                                                (= L3 M3)
                                                (= J3 (DOMPath nilInt K3))
                                                (= N3 J3)
                                                (= H3 I3))
                                           a!84))
                                 (a!111 (= (ite a!104
                                                (@0ArrayResponse (responses Q2))
                                                a!110)
                                           J4))
                                 (a!197 (or (and (= a!184
                                                    (ite a!185 a!186 a!192))
                                                 a!193)
                                            a!195
                                            (= (ft_emitter E4) EmitterWorker)
                                            a!196
                                            (= (ft_emitter E4) EmitterClient))))
                           (let ((a!39 (and a!29
                                            (= a!37
                                               (SomeDOMElement (@0SomeDOMElement a!37)))
                                            a!38
                                            (= M2 H2)
                                            (= P2 X1)
                                            (= G1 I2)
                                            (= (@0DOMElementForm (@0SomeDOMElement a!37))
                                               I2)
                                            (= J2 (EmitterForm H1 G1))
                                            (= H1 E2)
                                            (= E2 (DOMPath F2 (DOMIndex G2)))
                                            (= Q2 Y1)))
                                 (a!68 (and a!56
                                            (= a!64
                                               (SomeDOMElement (@0SomeDOMElement a!64)))
                                            a!65
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!64))
                                               a!66)
                                            (= M2 E1)
                                            (= P2 U)
                                            (= D F1)
                                            a!67
                                            (= J2 (EmitterScript E D))
                                            (= B1 (DOMPath C1 (DOMIndex D1)))
                                            (= E B1)
                                            (= Q2 V)))
                                 (a!100 (and a!85
                                             (= a!93
                                                (SomeDOMElement (@0SomeDOMElement a!93)))
                                             a!94
                                             (= (@1DOMElementResource
                                                  (@0SomeDOMElement a!93))
                                                a!95)
                                             (= M2 Q3)
                                             (= P2 G3)
                                             (= N2 R3)
                                             a!96
                                             (= J2 (EmitterCORSPreflight L2 K2))
                                             a!99
                                             (= O2 N3)
                                             (= N3 (DOMPath O3 (DOMIndex P3)))
                                             (= Q2 H3)))
                                 (a!112 (and (not (= (url_protocol a!101)
                                                     ProtocolData))
                                             (not (= (url_protocol a!101)
                                                     ProtocolBlob))
                                             (= (url_protocol (rp_url J4))
                                                ProtocolHTTP)
                                             a!111))
                                 (a!113 (and (not (= (url_protocol a!101)
                                                     ProtocolData))
                                             (not (= (url_protocol a!101)
                                                     ProtocolBlob))
                                             (= (url_protocol (rp_url J4))
                                                ProtocolHTTPS)
                                             a!111))
                                 (a!198 (and a!197
                                             (= (rp_hd_access_control_allow_origin
                                                  (rp_headers J4))
                                                a!184))))
                           (let ((a!199 (or (= (rp_hd_access_control_allow_origin
                                                 (rp_headers J4))
                                               NoneOrigin)
                                            a!198)))
                           (let ((a!200 (and (Reachable Q2 L4 A)
                                             (= A
                                                (Build_State M4
                                                             E4
                                                             O4
                                                             P2
                                                             I4
                                                             Q4
                                                             R4))
                                             (= B
                                                (Build_State (+ 1 M4)
                                                             N4
                                                             O4
                                                             P2
                                                             P4
                                                             Q4
                                                             R4))
                                             a!3
                                             (= N4
                                                (Build_FetchEngine
                                                  (+ 1 M4)
                                                  (ft_emitter E4)
                                                  (ft_request E4)
                                                  (ft_correlator E4)
                                                  (SomeResponse J4)
                                                  a!9))
                                             (= (rp_url J4)
                                                (rq_url (ft_request E4)))
                                             (= (ft_response E4) NoneResponse)
                                             a!12
                                             (= J2 (ft_emitter E4))
                                             (= K4 (ft_correlator E4))
                                             (or (and (= M2 P2)
                                                      (= J2 EmitterClient))
                                                 (and (= M2 P2)
                                                      (= J2 EmitterWorker))
                                                 a!39
                                                 a!68
                                                 a!100)
                                             (or a!112 a!113 a!121 a!129)
                                             (or a!130 a!183)
                                             a!199
                                             (= C
                                                (consEvent (EvResponse J4 K4)
                                                           L4)))))
                             (=> a!200 (Reachable Q2 C B)))))))))))
                           :weight 0))))
      (a!91 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 3) 1))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 3))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!93 (asserted (forall ((A State)
                               (B State)
                               (C listEvent)
                               (D Script)
                               (E NestedDOMPath)
                               (F NestedDOMPath)
                               (G Int)
                               (H Window)
                               (I HTML)
                               (J Frame)
                               (K listInt)
                               (L DOMSelector)
                               (M Window)
                               (N Window)
                               (O Global)
                               (P Global)
                               (Q NestedDOMPath)
                               (R DOMSelector)
                               (S Window)
                               (T Window)
                               (U Window)
                               (V Global)
                               (W Global)
                               (X NestedDOMPath)
                               (Y DOMSelector)
                               (Z Window)
                               (A1 Window)
                               (B1 NestedDOMPath)
                               (C1 listInt)
                               (D1 Int)
                               (E1 Window)
                               (F1 Script)
                               (G1 Form)
                               (H1 NestedDOMPath)
                               (I1 NestedDOMPath)
                               (J1 Int)
                               (K1 Window)
                               (L1 HTML)
                               (M1 Frame)
                               (N1 listInt)
                               (O1 DOMSelector)
                               (P1 Window)
                               (Q1 Window)
                               (R1 Global)
                               (S1 Global)
                               (T1 NestedDOMPath)
                               (U1 DOMSelector)
                               (V1 Window)
                               (W1 Window)
                               (X1 Window)
                               (Y1 Global)
                               (Z1 Global)
                               (A2 NestedDOMPath)
                               (B2 DOMSelector)
                               (C2 Window)
                               (D2 Window)
                               (E2 NestedDOMPath)
                               (F2 listInt)
                               (G2 Int)
                               (H2 Window)
                               (I2 Form)
                               (J2 Emitter)
                               (K2 Request)
                               (L2 Int)
                               (M2 Window)
                               (N2 Script)
                               (O2 NestedDOMPath)
                               (P2 Window)
                               (Q2 Global)
                               (R2 NestedDOMPath)
                               (S2 Int)
                               (T2 Window)
                               (U2 HTML)
                               (V2 Frame)
                               (W2 listInt)
                               (X2 DOMSelector)
                               (Y2 Window)
                               (Z2 Window)
                               (A3 Global)
                               (B3 Global)
                               (C3 NestedDOMPath)
                               (D3 DOMSelector)
                               (E3 Window)
                               (F3 Window)
                               (G3 Window)
                               (H3 Global)
                               (I3 Global)
                               (J3 NestedDOMPath)
                               (K3 DOMSelector)
                               (L3 Window)
                               (M3 Window)
                               (N3 NestedDOMPath)
                               (O3 listInt)
                               (P3 Int)
                               (Q3 Window)
                               (R3 Script)
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
                               (E4 Int)
                               (F4 listEvent)
                               (G4 Int)
                               (H4 FetchEngine)
                               (I4 ServiceWorker)
                               (J4 ArrayoptionSetCookie)
                               (K4 ArrayoptionBlob)
                               (L4 ArrayoptionStorageItem))
                        (! (let ((a!1 (= (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))
                                         0))
                                 (a!2 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M2)))))
                                 (a!3 (= (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))
                                         1))
                                 (a!4 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M2)))))
                                 (a!5 (= (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))
                                         2))
                                 (a!6 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M2)))))
                                 (a!7 (= (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))
                                         3))
                                 (a!8 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document M2)))))
                                 (a!9 (= (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))
                                         4))
                                 (a!10 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!11 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M2)))))
                                 (a!17 (= (@0EmitterScript J2)
                                          (DOMPath (@0DOMPath (@0EmitterScript J2))
                                                   (@1DOMPath (@0EmitterScript J2)))))
                                 (a!18 (DOMIndex (@0DOMIndex (@1DOMPath (@0EmitterScript J2)))))
                                 (a!20 (and (c_earlyhtml5_form_methods
                                              (config Q2))
                                            (= (form_method (@1EmitterForm J2))
                                               MethodPut)))
                                 (a!21 (and (c_earlyhtml5_form_methods
                                              (config Q2))
                                            (= (form_method (@1EmitterForm J2))
                                               MethodDelete)))
                                 (a!23 (= (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))
                                          0))
                                 (a!24 (= (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))
                                          1))
                                 (a!25 (= (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))
                                          2))
                                 (a!26 (= (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))
                                          3))
                                 (a!27 (= (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))
                                          4))
                                 (a!32 (= (@0EmitterForm J2)
                                          (DOMPath (@0DOMPath (@0EmitterForm J2))
                                                   (@1DOMPath (@0EmitterForm J2)))))
                                 (a!33 (DOMIndex (@0DOMIndex (@1DOMPath (@0EmitterForm J2)))))
                                 (a!35 ((_ is ProtocolHTTPS)
                                         (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                 J2)))))
                                 (a!36 ((_ is ProtocolHTTP)
                                         (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                 J2)))))
                                 (a!37 (TupleOrigin (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                            J2)))
                                                    (url_host (rq_url (@1EmitterCORSPreflight
                                                                        J2)))
                                                    (url_port (rq_url (@1EmitterCORSPreflight
                                                                        J2)))))
                                 (a!38 ((_ is ProtocolData)
                                         (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                 J2)))))
                                 (a!39 ((_ is url_path_data)
                                         (url_path (rq_url (@1EmitterCORSPreflight
                                                             J2)))))
                                 (a!40 (@0url_path_data (url_path (rq_url (@1EmitterCORSPreflight
                                                                            J2)))))
                                 (a!41 ((_ is url_path_blob)
                                         (url_path (rq_url (@1EmitterCORSPreflight
                                                             J2)))))
                                 (a!42 (@0url_path_blob (url_path (rq_url (@1EmitterCORSPreflight
                                                                            J2)))))
                                 (a!45 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location M2)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location M2)))))
                                 (a!46 (SomeOrigin (TupleOrigin (url_protocol (wd_location M2))
                                                                (url_host (wd_location M2))
                                                                (url_port (wd_location M2)))))
                                 (a!47 (OpaqueOrigin (@0url_path_data (url_path (wd_location M2)))))
                                 (a!49 (SomeOrigin (@0url_path_blob (url_path (wd_location M2)))))
                                 (a!54 (not (= (rq_method (@1EmitterCORSPreflight
                                                            J2))
                                               MethodGet)))
                                 (a!55 (not (= (rq_method (@1EmitterCORSPreflight
                                                            J2))
                                               MethodPost)))
                                 (a!57 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!58 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!59 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!60 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!61 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!62 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document K1)))))
                                 (a!69 (ite (= (frame_window M1) 3)
                                            (@3ArrayWindow (windows R1))
                                            (ite (= (frame_window M1) 4)
                                                 (@4ArrayWindow (windows R1))
                                                 (@defaultArrayWindow
                                                   (windows R1)))))
                                 (a!74 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!75 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!76 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!77 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!78 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!79 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H2)))))
                                 (a!84 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!85 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!86 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!87 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!88 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!89 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!96 (ite (= (frame_window J) 3)
                                            (@3ArrayWindow (windows O))
                                            (ite (= (frame_window J) 4)
                                                 (@4ArrayWindow (windows O))
                                                 (@defaultArrayWindow
                                                   (windows O)))))
                                 (a!101 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!102 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!103 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!104 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!105 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!106 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E1)))))
                                 (a!113 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!114 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!115 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!116 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!117 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!118 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T2)))))
                                 (a!125 (ite (= (frame_window V2) 3)
                                             (@3ArrayWindow (windows A3))
                                             (ite (= (frame_window V2) 4)
                                                  (@4ArrayWindow (windows A3))
                                                  (@defaultArrayWindow
                                                    (windows A3)))))
                                 (a!130 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!131 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!132 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!133 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!134 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!135 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q3)))))
                                 (a!141 (ite (= L2 3)
                                             (@3ArrayEmitter (emitters Q2))
                                             (ite (= L2 4)
                                                  (@4ArrayEmitter (emitters Q2))
                                                  (@defaultArrayEmitter
                                                    (emitters Q2)))))
                                 (a!145 (url_path_res (@0url_path_res (url_path (rq_url D4)))))
                                 (a!146 (SomeDomain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!147 (SomeInt (@0SomeInt (url_port (rq_url D4)))))
                                 (a!150 (url_path_data (@0url_path_data (url_path (rq_url D4)))
                                                       (@1url_path_data (url_path (rq_url D4)))))
                                 (a!152 (url_path_blob (@0url_path_blob (url_path (rq_url D4)))
                                                       (@1url_path_blob (url_path (rq_url D4)))))
                                 (a!154 (not (sc_secure (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                           J4)))))
                                 (a!156 ((_ is domain)
                                          (@0SomeDomain (url_host (wd_location M2)))))
                                 (a!157 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            J4)))))
                                 (a!158 (@0domain (@0SomeDomain (url_host (wd_location M2)))))
                                 (a!159 (@0domain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!160 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!161 (@1subdomain (@0SomeDomain (url_host (wd_location M2)))))
                                 (a!162 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!163 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!166 (not ((_ is url_path_blob)
                                               (url_path (rq_url D4)))))
                                 (a!167 (not ((_ is url_path_data)
                                               (url_path (rq_url D4)))))
                                 (a!168 ((_ is slash)
                                          (@0url_path_res (url_path (rq_url D4)))))
                                 (a!169 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                      J4)))))
                                 (a!170 (@0anypath (@0url_path_res (url_path (rq_url D4)))))
                                 (a!171 (@0anypath (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                               J4)))))
                                 (a!172 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        J4)))))
                                 (a!173 ((_ is domain)
                                          (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!174 (@0domain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!175 (@0SomeDomain (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!176 (@1subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!177 (@0subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!181 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!184 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       J4)))))
                                 (a!186 (not (sc_secure (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                           J4)))))
                                 (a!188 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            J4)))))
                                 (a!189 (@0domain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!190 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!191 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!192 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!195 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                      J4)))))
                                 (a!196 (@0anypath (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                               J4)))))
                                 (a!197 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        J4)))))
                                 (a!198 (@0SomeDomain (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!202 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!205 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       J4)))))
                                 (a!207 (not (sc_secure (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                           J4)))))
                                 (a!209 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            J4)))))
                                 (a!210 (@0domain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!211 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!212 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!213 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!216 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      J4)))))
                                 (a!217 (@0anypath (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                               J4)))))
                                 (a!218 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        J4)))))
                                 (a!219 (@0SomeDomain (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!223 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!226 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       J4)))))
                                 (a!228 (not (sc_secure (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                           J4)))))
                                 (a!230 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            J4)))))
                                 (a!231 (@0domain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!232 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!233 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!234 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!237 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      J4)))))
                                 (a!238 (@0anypath (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                               J4)))))
                                 (a!239 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        J4)))))
                                 (a!240 (@0SomeDomain (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!244 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!247 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       J4)))))
                                 (a!249 (not (sc_secure (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                           J4)))))
                                 (a!251 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            J4)))))
                                 (a!252 (@0domain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!253 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!254 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!255 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!258 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      J4)))))
                                 (a!259 (@0anypath (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                               J4)))))
                                 (a!260 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        J4)))))
                                 (a!261 (@0SomeDomain (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!265 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!268 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       J4)))))
                                 (a!270 (not (sc_secure (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                           J4)))))
                                 (a!272 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            J4)))))
                                 (a!273 (@0domain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!274 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                       J4)))))
                                 (a!275 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            J4)))
                                           SSLax))
                                 (a!276 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            J4)))
                                           SSNone))
                                 (a!279 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      J4)))))
                                 (a!280 (@0anypath (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                               J4)))))
                                 (a!281 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        J4)))))
                                 (a!282 (@0SomeDomain (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    J4)))))
                                 (a!286 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             J4)))
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                 (a!289 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      J4)))
                                          (sc_value (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       J4)))))
                                 (a!294 (= (rq_hd_cookie (rq_headers D4))
                                           (Build_ArrayoptionCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping)))
                                 (a!296 (ite (= Z3 2)
                                             (@2ArrayoptionBlob K4)
                                             (ite (= Z3 3)
                                                  (@3ArrayoptionBlob K4)
                                                  (ite (= Z3 4)
                                                       (@4ArrayoptionBlob K4)
                                                       (@defaultArrayoptionBlob
                                                         K4)))))
                                 (a!299 (and (= (rq_hd_origin (rq_headers D4))
                                                NoneOrigin)
                                             (= (rq_method D4) MethodGet)
                                             (= J2 EmitterClient)
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)))
                                 (a!302 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rq_url D4)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rq_url D4)))))
                                 (a!303 (SomeOrigin (TupleOrigin (url_protocol (rq_url D4))
                                                                 (url_host (rq_url D4))
                                                                 (url_port (rq_url D4)))))
                                 (a!304 (OpaqueOrigin (@0url_path_data (url_path (rq_url D4)))))
                                 (a!306 (SomeOrigin (@0url_path_blob (url_path (rq_url D4)))))
                                 (a!310 ((_ is SomeReferrerPolicy)
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document M2)))))
                                 (a!311 (@0SomeReferrerPolicy
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document M2)))))
                                 (a!320 (rp_hd_access_control_allow_origin
                                          (rp_headers (@0SomeResponse (ft_response C4)))))
                                 (a!321 (SomeOrigin (@0SomeOrigin (rq_hd_origin (rq_headers D4)))))
                                 (a!322 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                4)
                                             (@4ArrayEmitter (emitters Q2))
                                             (@defaultArrayEmitter
                                               (emitters Q2))))
                                 (a!327 (= (ft_emitter C4)
                                           (EmitterCORSPreflight
                                             (@0EmitterCORSPreflight
                                               (ft_emitter C4))
                                             (@1EmitterCORSPreflight
                                               (ft_emitter C4)))))
                                 (a!328 (= (ft_response C4)
                                           (SomeResponse (@0SomeResponse (ft_response C4)))))
                                 (a!334 (and (or (= J2 EmitterClient)
                                                 (= J2 EmitterWorker)
                                                 (= J2 (EmitterForm V3 W3))
                                                 (= J2 (EmitterScript T3 U3)))
                                             (not (c_redirect_preflight_requests
                                                    (config Q2)))))
                                 (a!336 (= (rq_hd_origin (rq_headers D4))
                                           (rq_hd_origin (rq_headers (ft_request C4)))))
                                 (a!337 ((_ is ProtocolHTTPS)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!338 ((_ is ProtocolHTTP)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!339 (TupleOrigin (url_protocol (rq_url (ft_request C4)))
                                                     (url_host (rq_url (ft_request C4)))
                                                     (url_port (rq_url (ft_request C4)))))
                                 (a!340 ((_ is ProtocolData)
                                          (url_protocol (rq_url (ft_request C4)))))
                                 (a!341 ((_ is url_path_data)
                                          (url_path (rq_url (ft_request C4)))))
                                 (a!342 (@0url_path_data (url_path (rq_url (ft_request C4)))))
                                 (a!343 ((_ is url_path_blob)
                                          (url_path (rq_url (ft_request C4)))))
                                 (a!344 (@0url_path_blob (url_path (rq_url (ft_request C4))))))
                           (let ((a!12 (ite a!3
                                            a!4
                                            (ite a!5
                                                 a!6
                                                 (ite a!7
                                                      a!8
                                                      (ite a!9 a!10 a!11)))))
                                 (a!22 (or (= (form_method (@1EmitterForm J2))
                                              MethodPost)
                                           (= (form_method (@1EmitterForm J2))
                                              MethodGet)
                                           a!20
                                           a!21))
                                 (a!28 (ite a!24
                                            a!4
                                            (ite a!25
                                                 a!6
                                                 (ite a!26
                                                      a!8
                                                      (ite a!27 a!10 a!11)))))
                                 (a!43 (ite a!38
                                            (ite a!39
                                                 (SomeOrigin (OpaqueOrigin a!40))
                                                 NoneOrigin)
                                            (ite a!39
                                                 NoneOrigin
                                                 (ite a!41
                                                      (SomeOrigin a!42)
                                                      NoneOrigin))))
                                 (a!48 (ite ((_ is url_path_data)
                                              (url_path (wd_location M2)))
                                            (SomeOrigin a!47)
                                            NoneOrigin))
                                 (a!50 (ite ((_ is url_path_blob)
                                              (url_path (wd_location M2)))
                                            a!49
                                            NoneOrigin))
                                 (a!63 (ite (= J1 2)
                                            a!59
                                            (ite (= J1 3)
                                                 a!60
                                                 (ite (= J1 4) a!61 a!62))))
                                 (a!70 (ite (= (frame_window M1) 1)
                                            (@1ArrayWindow (windows R1))
                                            (ite (= (frame_window M1) 2)
                                                 (@2ArrayWindow (windows R1))
                                                 a!69)))
                                 (a!80 (ite (= G2 2)
                                            a!76
                                            (ite (= G2 3)
                                                 a!77
                                                 (ite (= G2 4) a!78 a!79))))
                                 (a!90 (ite (= G 2)
                                            a!86
                                            (ite (= G 3)
                                                 a!87
                                                 (ite (= G 4) a!88 a!89))))
                                 (a!97 (ite (= (frame_window J) 1)
                                            (@1ArrayWindow (windows O))
                                            (ite (= (frame_window J) 2)
                                                 (@2ArrayWindow (windows O))
                                                 a!96)))
                                 (a!107 (ite (= D1 2)
                                             a!103
                                             (ite (= D1 3)
                                                  a!104
                                                  (ite (= D1 4) a!105 a!106))))
                                 (a!119 (ite (= S2 2)
                                             a!115
                                             (ite (= S2 3)
                                                  a!116
                                                  (ite (= S2 4) a!117 a!118))))
                                 (a!126 (ite (= (frame_window V2) 1)
                                             (@1ArrayWindow (windows A3))
                                             (ite (= (frame_window V2) 2)
                                                  (@2ArrayWindow (windows A3))
                                                  a!125)))
                                 (a!136 (ite (= P3 2)
                                             a!132
                                             (ite (= P3 3)
                                                  a!133
                                                  (ite (= P3 4) a!134 a!135))))
                                 (a!142 (ite (= L2 1)
                                             (@1ArrayEmitter (emitters Q2))
                                             (ite (= L2 2)
                                                  (@2ArrayEmitter (emitters Q2))
                                                  a!141)))
                                 (a!148 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTP)
                                             (= (url_path (rq_url D4)) a!145)
                                             (= (url_host (rq_url D4)) a!146)
                                             (= (url_port (rq_url D4)) a!147)))
                                 (a!149 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)
                                             (= (url_path (rq_url D4)) a!145)
                                             (= (url_host (rq_url D4)) a!146)
                                             (= (url_port (rq_url D4)) a!147)))
                                 (a!151 (and (= (url_protocol (rq_url D4))
                                                ProtocolData)
                                             (= (url_path (rq_url D4)) a!150)
                                             (= (url_host (rq_url D4))
                                                NoneDomain)
                                             (= (url_port (rq_url D4)) NoneInt)))
                                 (a!153 (and (= (url_protocol (rq_url D4))
                                                ProtocolBlob)
                                             (= (url_path (rq_url D4)) a!152)
                                             (= (url_host (rq_url D4))
                                                NoneDomain)
                                             (= (url_port (rq_url D4)) NoneInt)))
                                 (a!155 (or a!154
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!164 (ite ((_ is EmitterClient) J2)
                                             (or a!162 a!163)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!163
                                                  (and a!163
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!178 (ite ((_ is domain) a!175)
                                             (= a!176 (@0domain a!175))
                                             (and (= a!177 (@0subdomain a!175))
                                                  (= a!176 (@1subdomain a!175)))))
                                 (a!182 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!181))
                                 (a!187 (or a!186
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!193 (ite ((_ is EmitterClient) J2)
                                             (or a!191 a!192)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!192
                                                  (and a!192
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!199 (ite ((_ is domain) a!198)
                                             (= a!176 (@0domain a!198))
                                             (and (= a!177 (@0subdomain a!198))
                                                  (= a!176 (@1subdomain a!198)))))
                                 (a!203 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!202))
                                 (a!208 (or a!207
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!214 (ite ((_ is EmitterClient) J2)
                                             (or a!212 a!213)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!213
                                                  (and a!213
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!220 (ite ((_ is domain) a!219)
                                             (= a!176 (@0domain a!219))
                                             (and (= a!177 (@0subdomain a!219))
                                                  (= a!176 (@1subdomain a!219)))))
                                 (a!224 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!223))
                                 (a!229 (or a!228
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!235 (ite ((_ is EmitterClient) J2)
                                             (or a!233 a!234)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!234
                                                  (and a!234
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!241 (ite ((_ is domain) a!240)
                                             (= a!176 (@0domain a!240))
                                             (and (= a!177 (@0subdomain a!240))
                                                  (= a!176 (@1subdomain a!240)))))
                                 (a!245 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!244))
                                 (a!250 (or a!249
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!256 (ite ((_ is EmitterClient) J2)
                                             (or a!254 a!255)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!255
                                                  (and a!255
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!262 (ite ((_ is domain) a!261)
                                             (= a!176 (@0domain a!261))
                                             (and (= a!177 (@0subdomain a!261))
                                                  (= a!176 (@1subdomain a!261)))))
                                 (a!266 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!265))
                                 (a!271 (or a!270
                                            (= (url_protocol (rq_url D4))
                                               ProtocolHTTPS)))
                                 (a!277 (ite ((_ is EmitterClient) J2)
                                             (or a!275 a!276)
                                             (ite (or ((_ is EmitterForm) J2)
                                                      ((_ is EmitterScript) J2))
                                                  a!276
                                                  (and a!276
                                                       ((_ is EmitterWorker) J2)))))
                                 (a!283 (ite ((_ is domain) a!282)
                                             (= a!176 (@0domain a!282))
                                             (and (= a!177 (@0subdomain a!282))
                                                  (= a!176 (@1subdomain a!282)))))
                                 (a!287 (and ((_ is SomeDomain)
                                               (url_host (rq_url D4)))
                                             a!286))
                                 (a!295 (and (= J2 EmitterClient)
                                             (= (url_protocol (rq_url D4))
                                                ProtocolData)
                                             a!294))
                                 (a!297 (= (ite (= Z3 0)
                                                (@0ArrayoptionBlob K4)
                                                (ite (= Z3 1)
                                                     (@1ArrayoptionBlob K4)
                                                     a!296))
                                           (SomeBlob A4)))
                                 (a!305 (ite ((_ is url_path_data)
                                               (url_path (rq_url D4)))
                                             (SomeOrigin a!304)
                                             NoneOrigin))
                                 (a!307 (ite ((_ is url_path_blob)
                                               (url_path (rq_url D4)))
                                             a!306
                                             NoneOrigin))
                                 (a!323 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                3)
                                             (@3ArrayEmitter (emitters Q2))
                                             a!322))
                                 (a!329 (= (@0SomeOrigin a!320)
                                           (@0SomeOrigin (rq_hd_origin (rq_headers D4)))))
                                 (a!345 (ite a!340
                                             (ite a!341
                                                  (SomeOrigin (OpaqueOrigin a!342))
                                                  NoneOrigin)
                                             (ite a!341
                                                  NoneOrigin
                                                  (ite a!343
                                                       (SomeOrigin a!344)
                                                       NoneOrigin)))))
                           (let ((a!13 (= (ite a!1 a!2 a!12)
                                          (SomeDOMElement (@0SomeDOMElement (ite a!1
                                                                                 a!2
                                                                                 a!12)))))
                                 (a!14 (DOMElementResource
                                         (@0DOMElementResource
                                           (@0SomeDOMElement (ite a!1 a!2 a!12)))
                                         (@1DOMElementResource
                                           (@0SomeDOMElement (ite a!1 a!2 a!12)))))
                                 (a!15 (@0ContentElementScript
                                         (@1DOMElementResource
                                           (@0SomeDOMElement (ite a!1 a!2 a!12)))))
                                 (a!29 (= (ite a!23 a!2 a!28)
                                          (SomeDOMElement (@0SomeDOMElement (ite a!23
                                                                                 a!2
                                                                                 a!28)))))
                                 (a!30 (DOMElementForm (@0DOMElementForm (@0SomeDOMElement (ite a!23
                                                                                                a!2
                                                                                                a!28)))))
                                 (a!31 (= (@0DOMElementForm (@0SomeDOMElement (ite a!23
                                                                                   a!2
                                                                                   a!28)))
                                          (@1EmitterForm J2)))
                                 (a!44 (not (= (ite (or a!35 a!36)
                                                    (SomeOrigin a!37)
                                                    a!43)
                                               NoneOrigin)))
                                 (a!51 (ite ((_ is url_path_data)
                                              (url_path (wd_location M2)))
                                            NoneOrigin
                                            a!50))
                                 (a!64 (ite (= J1 0)
                                            a!57
                                            (ite (= J1 1) a!58 a!63)))
                                 (a!71 (= (ite (= (frame_window M1) 0)
                                               (@0ArrayWindow (windows R1))
                                               a!70)
                                          P1))
                                 (a!81 (ite (= G2 0)
                                            a!74
                                            (ite (= G2 1) a!75 a!80)))
                                 (a!91 (ite (= G 0)
                                            a!84
                                            (ite (= G 1) a!85 a!90)))
                                 (a!98 (= (ite (= (frame_window J) 0)
                                               (@0ArrayWindow (windows O))
                                               a!97)
                                          M))
                                 (a!108 (ite (= D1 0)
                                             a!101
                                             (ite (= D1 1) a!102 a!107)))
                                 (a!120 (ite (= S2 0)
                                             a!113
                                             (ite (= S2 1) a!114 a!119)))
                                 (a!127 (= (ite (= (frame_window V2) 0)
                                                (@0ArrayWindow (windows A3))
                                                a!126)
                                           Y2))
                                 (a!137 (ite (= P3 0)
                                             a!130
                                             (ite (= P3 1) a!131 a!136)))
                                 (a!143 (= (ite (= L2 0)
                                                (@0ArrayEmitter (emitters Q2))
                                                a!142)
                                           (EmitterScript O2 N2)))
                                 (a!165 (or (ite a!156
                                                 (ite a!157
                                                      (= a!158 a!159)
                                                      (= a!158 a!160))
                                                 (ite a!157
                                                      (= a!161 a!159)
                                                      (= a!161 a!160)))
                                            a!164))
                                 (a!179 (ite a!173
                                             (and (= a!174 (@0domain a!175))
                                                  ((_ is domain) a!175))
                                             a!178))
                                 (a!194 (or (ite a!156
                                                 (ite a!188
                                                      (= a!158 a!189)
                                                      (= a!158 a!190))
                                                 (ite a!188
                                                      (= a!161 a!189)
                                                      (= a!161 a!190)))
                                            a!193))
                                 (a!200 (ite a!173
                                             (and (= a!174 (@0domain a!198))
                                                  ((_ is domain) a!198))
                                             a!199))
                                 (a!215 (or (ite a!156
                                                 (ite a!209
                                                      (= a!158 a!210)
                                                      (= a!158 a!211))
                                                 (ite a!209
                                                      (= a!161 a!210)
                                                      (= a!161 a!211)))
                                            a!214))
                                 (a!221 (ite a!173
                                             (and (= a!174 (@0domain a!219))
                                                  ((_ is domain) a!219))
                                             a!220))
                                 (a!236 (or (ite a!156
                                                 (ite a!230
                                                      (= a!158 a!231)
                                                      (= a!158 a!232))
                                                 (ite a!230
                                                      (= a!161 a!231)
                                                      (= a!161 a!232)))
                                            a!235))
                                 (a!242 (ite a!173
                                             (and (= a!174 (@0domain a!240))
                                                  ((_ is domain) a!240))
                                             a!241))
                                 (a!257 (or (ite a!156
                                                 (ite a!251
                                                      (= a!158 a!252)
                                                      (= a!158 a!253))
                                                 (ite a!251
                                                      (= a!161 a!252)
                                                      (= a!161 a!253)))
                                            a!256))
                                 (a!263 (ite a!173
                                             (and (= a!174 (@0domain a!261))
                                                  ((_ is domain) a!261))
                                             a!262))
                                 (a!278 (or (ite a!156
                                                 (ite a!272
                                                      (= a!158 a!273)
                                                      (= a!158 a!274))
                                                 (ite a!272
                                                      (= a!161 a!273)
                                                      (= a!161 a!274)))
                                            a!277))
                                 (a!284 (ite a!173
                                             (and (= a!174 (@0domain a!282))
                                                  ((_ is domain) a!282))
                                             a!283))
                                 (a!298 (and (= J2 EmitterClient)
                                             (= (url_protocol (rq_url D4))
                                                ProtocolBlob)
                                             (= (url_path (rq_url D4))
                                                (url_path_blob B4 Z3))
                                             (= (blob_origin A4) B4)
                                             (= (rq_url D4) (blob_url A4))
                                             a!294
                                             a!297))
                                 (a!308 (ite ((_ is url_path_data)
                                               (url_path (rq_url D4)))
                                             NoneOrigin
                                             a!307))
                                 (a!324 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                2)
                                             (@2ArrayEmitter (emitters Q2))
                                             a!323)))
                           (let ((a!16 (= (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!1 a!2 a!12)))
                                          (ContentElementScript a!15)))
                                 (a!34 (and a!22
                                            a!29
                                            (= (@0SomeDOMElement (ite a!23
                                                                      a!2
                                                                      a!28))
                                               a!30)
                                            a!31
                                            (= J2
                                               (EmitterForm (@0EmitterForm J2)
                                                            (@1EmitterForm J2)))
                                            a!32
                                            (= (@1DOMPath (@0EmitterForm J2))
                                               a!33)))
                                 (a!52 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location M2)))
                                            a!48
                                            a!51))
                                 (a!65 (= (@0SomeDOMElement a!64)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!64))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!64)))))
                                 (a!66 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!64)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!64)))))
                                 (a!67 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!64)))
                                          M1))
                                 (a!68 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!64)))
                                          L1))
                                 (a!82 (= (@0SomeDOMElement a!81)
                                          (DOMElementForm (@0DOMElementForm (@0SomeDOMElement a!81)))))
                                 (a!92 (= (@0SomeDOMElement a!91)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!91))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!91)))))
                                 (a!93 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!91)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!91)))))
                                 (a!94 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!91)))
                                          J))
                                 (a!95 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!91)))
                                          I))
                                 (a!109 (= (@0SomeDOMElement a!108)
                                           (DOMElementResource
                                             (@0DOMElementResource
                                               (@0SomeDOMElement a!108))
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!108)))))
                                 (a!110 (ContentElementScript
                                          (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!108)))))
                                 (a!111 (= (@0ContentElementScript
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!108)))
                                           F1))
                                 (a!121 (= (@0SomeDOMElement a!120)
                                           (DOMElementResource
                                             (@0DOMElementResource
                                               (@0SomeDOMElement a!120))
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!120)))))
                                 (a!122 (ContentElementFrame
                                          (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!120)))
                                          (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!120)))))
                                 (a!123 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!120)))
                                           V2))
                                 (a!124 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!120)))
                                           U2))
                                 (a!138 (= (@0SomeDOMElement a!137)
                                           (DOMElementResource
                                             (@0DOMElementResource
                                               (@0SomeDOMElement a!137))
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!137)))))
                                 (a!139 (ContentElementScript
                                          (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!137)))))
                                 (a!140 (= (@0ContentElementScript
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!137)))
                                           R3))
                                 (a!180 (and a!179
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!201 (and a!200
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!222 (and a!221
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!243 (and a!242
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!264 (and a!263
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!285 (and a!284
                                             ((_ is SomeDomain)
                                               (url_host (rq_url D4)))))
                                 (a!309 (ite ((_ is ProtocolData)
                                               (url_protocol (rq_url D4)))
                                             a!305
                                             a!308))
                                 (a!325 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                1)
                                             (@1ArrayEmitter (emitters Q2))
                                             a!324)))
                           (let ((a!19 (and a!13
                                            (= (@0SomeDOMElement (ite a!1
                                                                      a!2
                                                                      a!12))
                                               a!14)
                                            a!16
                                            (= a!15 (@1EmitterScript J2))
                                            (= J2
                                               (EmitterScript (@0EmitterScript J2)
                                                              (@1EmitterScript J2)))
                                            a!17
                                            (= (@1DOMPath (@0EmitterScript J2))
                                               a!18)))
                                 (a!53 (not (= (ite (or a!35 a!36)
                                                    (SomeOrigin a!37)
                                                    a!43)
                                               (ite a!45 a!46 a!52))))
                                 (a!72 (and (= a!64
                                               (SomeDOMElement (@0SomeDOMElement a!64)))
                                            a!65
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!64))
                                               a!66)
                                            a!67
                                            a!68
                                            (= H2 Q1)
                                            (= X1 K1)
                                            (= V1 W1)
                                            (= Q1 V1)
                                            (= P1 W1)
                                            a!71
                                            (= E2 I1)
                                            (= T1 (DOMPath N1 O1))
                                            (= T1 (DOMPath nilInt U1))
                                            (= I1 (DOMPath (consInt J1 N1) O1))
                                            (= Y1 R1)
                                            (= R1 S1)))
                                 (a!99 (and (= a!91
                                               (SomeDOMElement (@0SomeDOMElement a!91)))
                                            a!92
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!91))
                                               a!93)
                                            a!94
                                            a!95
                                            (= U H)
                                            (= N S)
                                            (= E1 N)
                                            (= S T)
                                            (= M T)
                                            a!98
                                            (= B1 F)
                                            (= Q (DOMPath K L))
                                            (= Q (DOMPath nilInt R))
                                            (= F (DOMPath (consInt G K) L))
                                            (= V O)
                                            (= O P)))
                                 (a!128 (and (= a!120
                                                (SomeDOMElement (@0SomeDOMElement a!120)))
                                             a!121
                                             (= (@1DOMElementResource
                                                  (@0SomeDOMElement a!120))
                                                a!122)
                                             a!123
                                             a!124
                                             (= E3 F3)
                                             (= Q3 Z2)
                                             (= Z2 E3)
                                             (= G3 T2)
                                             (= Y2 F3)
                                             a!127
                                             (= R2 (DOMPath (consInt S2 W2) X2))
                                             (= C3 (DOMPath W2 X2))
                                             (= C3 (DOMPath nilInt D3))
                                             (= N3 R2)
                                             (= A3 B3)
                                             (= H3 A3)))
                                 (a!183 (and a!155
                                             a!165
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!169
                                                  (or a!169 (= a!170 a!171)))
                                             (ite a!172 a!180 a!182)))
                                 (a!204 (and a!187
                                             a!194
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!195
                                                  (or a!195 (= a!170 a!196)))
                                             (ite a!197 a!201 a!203)))
                                 (a!225 (and a!208
                                             a!215
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!216
                                                  (or a!216 (= a!170 a!217)))
                                             (ite a!218 a!222 a!224)))
                                 (a!246 (and a!229
                                             a!236
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!237
                                                  (or a!237 (= a!170 a!238)))
                                             (ite a!239 a!243 a!245)))
                                 (a!267 (and a!250
                                             a!257
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!258
                                                  (or a!258 (= a!170 a!259)))
                                             (ite a!260 a!264 a!266)))
                                 (a!288 (and a!271
                                             a!278
                                             a!166
                                             a!167
                                             (ite a!168
                                                  a!279
                                                  (or a!279 (= a!170 a!280)))
                                             (ite a!281 a!285 a!287)))
                                 (a!300 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!45
                                                                  a!46
                                                                  a!52)))
                                             (ite a!45 a!46 a!52)
                                             NoneOrigin))
                                 (a!312 (Build_URL (@0TupleOrigin (@0SomeOrigin (ite a!45
                                                                                     a!46
                                                                                     a!52)))
                                                   (@1TupleOrigin (@0SomeOrigin (ite a!45
                                                                                     a!46
                                                                                     a!52)))
                                                   (@2TupleOrigin (@0SomeOrigin (ite a!45
                                                                                     a!46
                                                                                     a!52)))
                                                   (url_path_res slash)))
                                 (a!316 (and (c_earlyhtml5_form_methods
                                               (config Q2))
                                             (not (= (ite a!302 a!303 a!309)
                                                     NoneOrigin))
                                             (= (ite a!302 a!303 a!309)
                                                (ite a!45 a!46 a!52))
                                             (= (form_method (@1EmitterForm J2))
                                                MethodPut)))
                                 (a!317 (and (c_earlyhtml5_form_methods
                                               (config Q2))
                                             (not (= (ite a!302 a!303 a!309)
                                                     NoneOrigin))
                                             (= (ite a!302 a!303 a!309)
                                                (ite a!45 a!46 a!52))
                                             (= (form_method (@1EmitterForm J2))
                                                MethodDelete)))
                                 (a!326 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter C4))
                                                0)
                                             (@0ArrayEmitter (emitters Q2))
                                             a!325))
                                 (a!346 (= (ite a!302 a!303 a!309)
                                           (ite (or a!337 a!338)
                                                (SomeOrigin a!339)
                                                a!345))))
                           (let ((a!56 (and a!44
                                            a!53
                                            a!54
                                            a!55
                                            (= J2
                                               (EmitterCORSPreflight
                                                 (@0EmitterCORSPreflight J2)
                                                 (@1EmitterCORSPreflight J2)))))
                                 (a!73 (or (and (= H2 C2)
                                                (= C2 D2)
                                                (= X1 D2)
                                                (= A2 (DOMPath nilInt B2))
                                                (= E2 A2)
                                                (= Y1 Z1))
                                           a!72))
                                 (a!100 (or (and (= U A1)
                                                 (= Z A1)
                                                 (= E1 Z)
                                                 (= X (DOMPath nilInt Y))
                                                 (= B1 X)
                                                 (= V W))
                                            a!99))
                                 (a!129 (or (and (= L3 M3)
                                                 (= Q3 L3)
                                                 (= G3 M3)
                                                 (= J3 (DOMPath nilInt K3))
                                                 (= N3 J3)
                                                 (= H3 I3))
                                            a!128))
                                 (a!185 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!183
                                                  (SomeCookieMapping a!184)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!206 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!204
                                                  (SomeCookieMapping a!205)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!227 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!225
                                                  (SomeCookieMapping a!226)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!248 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!246
                                                  (SomeCookieMapping a!247)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!269 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!267
                                                  (SomeCookieMapping a!268)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!290 (ite ((_ is SomeDomain)
                                               (url_host (wd_location M2)))
                                             (ite a!288
                                                  (SomeCookieMapping a!289)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!301 (= (rq_hd_origin (rq_headers D4))
                                           (ite ((_ is SomeOrigin)
                                                  (ite a!45 a!46 a!52))
                                                a!300
                                                (ite a!45 a!46 a!52))))
                                 (a!313 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!45
                                                                  a!46
                                                                  a!52)))
                                             (SomeURL a!312)
                                             NoneURL))
                                 (a!318 (or (= (form_method (@1EmitterForm J2))
                                               MethodOptions)
                                            (= (form_method (@1EmitterForm J2))
                                               MethodPost)
                                            (= (form_method (@1EmitterForm J2))
                                               MethodGet)
                                            a!316
                                            a!317))
                                 (a!330 (and (= a!320
                                                (SomeOrigin (@0SomeOrigin a!320)))
                                             (= (rq_hd_origin (rq_headers D4))
                                                a!321)
                                             (= J2 a!326)
                                             a!327
                                             (= D4
                                                (@1EmitterCORSPreflight
                                                  (ft_emitter C4)))
                                             a!328
                                             a!329))
                                 (a!347 (and (= (rq_hd_origin (rq_headers D4))
                                                NoneOrigin)
                                             (not a!346))))
                           (let ((a!83 (and a!73
                                            (= a!81
                                               (SomeDOMElement (@0SomeDOMElement a!81)))
                                            a!82
                                            (= P2 X1)
                                            (= M2 H2)
                                            (= G1 I2)
                                            (= (@0DOMElementForm (@0SomeDOMElement a!81))
                                               I2)
                                            (= J2 (EmitterForm H1 G1))
                                            (= E2 (DOMPath F2 (DOMIndex G2)))
                                            (= H1 E2)
                                            (= Q2 Y1)))
                                 (a!112 (and a!100
                                             (= a!108
                                                (SomeDOMElement (@0SomeDOMElement a!108)))
                                             a!109
                                             (= (@1DOMElementResource
                                                  (@0SomeDOMElement a!108))
                                                a!110)
                                             (= P2 U)
                                             (= M2 E1)
                                             (= D F1)
                                             a!111
                                             (= J2 (EmitterScript E D))
                                             (= B1 (DOMPath C1 (DOMIndex D1)))
                                             (= E B1)
                                             (= Q2 V)))
                                 (a!144 (and a!129
                                             (= a!137
                                                (SomeDOMElement (@0SomeDOMElement a!137)))
                                             a!138
                                             (= (@1DOMElementResource
                                                  (@0SomeDOMElement a!137))
                                                a!139)
                                             (= P2 G3)
                                             (= M2 Q3)
                                             (= N2 R3)
                                             a!140
                                             (= J2 (EmitterCORSPreflight L2 K2))
                                             a!143
                                             (= O2 N3)
                                             (= N3 (DOMPath O3 (DOMIndex P3)))
                                             (= Q2 H3)))
                                 (a!291 (Build_ArrayoptionCookieMapping
                                          (ite ((_ is SomeSetCookie)
                                                 (@0ArrayoptionSetCookie J4))
                                               a!185
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@1ArrayoptionSetCookie J4))
                                               a!206
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@2ArrayoptionSetCookie J4))
                                               a!227
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@3ArrayoptionSetCookie J4))
                                               a!248
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@4ArrayoptionSetCookie J4))
                                               a!269
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@defaultArrayoptionSetCookie
                                                   J4))
                                               a!290
                                               NoneCookieMapping)))
                                 (a!314 (ite ((_ is ReferrerPolicyNoReferrer)
                                               a!311)
                                             NoneURL
                                             (ite ((_ is SomeOrigin)
                                                    (ite a!45 a!46 a!52))
                                                  a!313
                                                  NoneURL)))
                                 (a!331 (or (= (rq_method D4) MethodGet)
                                            (= (ite a!302 a!303 a!309)
                                               NoneOrigin)
                                            (= (ite a!302 a!303 a!309)
                                               (ite a!45 a!46 a!52))
                                            (= (rq_method D4) MethodPost)
                                            a!330))
                                 (a!348 (and (or (and a!336 a!346) a!347)
                                             (not (c_origin_header_on_cross_origin_redirect
                                                    (config Q2))))))
                           (let ((a!292 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTP)
                                             (= (rq_hd_cookie (rq_headers D4))
                                                a!291)))
                                 (a!293 (and (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)
                                             (= (rq_hd_cookie (rq_headers D4))
                                                a!291)))
                                 (a!315 (and a!301
                                             (not (= (ite a!302 a!303 a!309)
                                                     NoneOrigin))
                                             (not (= (ite a!302 a!303 a!309)
                                                     (ite a!45 a!46 a!52)))
                                             (= (rq_method D4) MethodOptions)
                                             (= J2
                                                (EmitterCORSPreflight
                                                  (@0EmitterCORSPreflight J2)
                                                  (@1EmitterCORSPreflight J2)))
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!310 a!314 NoneURL))
                                             (= (rq_url D4)
                                                (rq_url (@1EmitterCORSPreflight
                                                          J2)))))
                                 (a!319 (and a!318
                                             a!301
                                             (= (rq_method D4)
                                                (form_method (@1EmitterForm J2)))
                                             (= J2
                                                (EmitterForm (@0EmitterForm J2)
                                                             (@1EmitterForm J2)))
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!310 a!314 NoneURL))
                                             (= (rq_url D4)
                                                (form_action (@1EmitterForm J2)))))
                                 (a!332 (and a!331
                                             a!301
                                             (= J2
                                                (EmitterScript (@0EmitterScript J2)
                                                               (@1EmitterScript J2)))
                                             (= (rq_hd_referer (rq_headers D4))
                                                (ite a!310 a!314 NoneURL))))
                                 (a!333 (and a!331
                                             a!301
                                             (= J2 EmitterWorker)
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)))
                                 (a!349 (or (and (c_origin_header_on_cross_origin_redirect
                                                   (config Q2))
                                                 a!336)
                                            a!348)))
                           (let ((a!335 (and (or a!299 a!315 a!319 a!332 a!333)
                                             (= (rp_hd_location (rp_headers Y3))
                                                NoneURL)))
                                 (a!350 (and a!349
                                             (= (rq_method D4) MethodGet)
                                             (= (ft_emitter C4) J2)
                                             (= (rq_body D4) NoneInt)
                                             (= (rp_hd_location (rp_headers Y3))
                                                (SomeURL S3))
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)
                                             (= (rq_url D4) S3)))
                                 (a!352 (and a!349
                                             (= (rq_method D4)
                                                (rq_method (ft_request C4)))
                                             (= (ft_emitter C4) J2)
                                             (= (rq_body D4)
                                                (rq_body (ft_request C4)))
                                             (= (rp_hd_location (rp_headers Y3))
                                                (SomeURL X3))
                                             (= (rq_hd_referer (rq_headers D4))
                                                NoneURL)
                                             (= (rq_url D4) X3))))
                           (let ((a!351 (and (or (c_redirect_preflight_requests
                                                   (config Q2))
                                                 a!334)
                                             (or a!335 a!350)
                                             (= (rp_code Y3) ResponseFound)))
                                 (a!353 (and (or (c_redirect_preflight_requests
                                                   (config Q2))
                                                 a!334)
                                             (or a!335 a!352)
                                             (= (rp_code Y3)
                                                ResponseTemporaryRedirect))))
                           (let ((a!354 (or (and (or a!299
                                                     a!315
                                                     a!319
                                                     a!332
                                                     a!333)
                                                 (= (rp_code Y3) ResponseOk))
                                            (and (or a!299
                                                     a!315
                                                     a!319
                                                     a!332
                                                     a!333)
                                                 (= (rp_code Y3)
                                                    ResponseNoContent))
                                            a!351
                                            a!353)))
                           (let ((a!355 (or (and a!354
                                                 (= (ft_response C4)
                                                    (SomeResponse Y3)))
                                            (and (or a!299
                                                     a!315
                                                     a!319
                                                     a!332
                                                     a!333)
                                                 (= (ft_response C4)
                                                    NoneResponse)))))
                           (let ((a!356 (and (Reachable Q2 F4 A)
                                             (= A
                                                (Build_State G4
                                                             C4
                                                             I4
                                                             P2
                                                             J4
                                                             K4
                                                             L4))
                                             (= B
                                                (Build_State (+ 1 G4)
                                                             H4
                                                             I4
                                                             P2
                                                             J4
                                                             K4
                                                             L4))
                                             (= H4
                                                (Build_FetchEngine
                                                  (+ 1 G4)
                                                  J2
                                                  D4
                                                  E4
                                                  NoneResponse
                                                  (ft_history C4)))
                                             (= E4 (+ 1 (ft_correlator C4)))
                                             (or (= J2 EmitterClient)
                                                 (= J2 EmitterWorker)
                                                 a!19
                                                 a!34
                                                 a!56)
                                             (or (and (= M2 P2)
                                                      (= J2 EmitterClient))
                                                 (and (= M2 P2)
                                                      (= J2 EmitterWorker))
                                                 a!83
                                                 a!112
                                                 a!144)
                                             (or a!148 a!149 a!151 a!153)
                                             (or a!292 a!293 a!295 a!298)
                                             a!355
                                             (= C
                                                (consEvent (EvRequest J2 D4 E4)
                                                           F4)))))
                             (=> a!356 (Reachable Q2 C B)))))))))))))))
                           :weight 0))))
      (a!96 (forall ((A Global))
              (! (let ((a!1 (Build_URL ProtocolHTTP
                                       (SomeDomain (subdomain 30 31))
                                       (SomeInt 32)
                                       (url_path_res (anypath 45))))
                       (a!2 (SomeTrustedTypes (Build_TrustedTypes
                                                (SomeoptionInt (SomeInt 123))
                                                false)))
                       (a!5 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 63)
                                                                   (url_path_data 64
                                                                                  65)))))
                       (a!6 (Build_URL ProtocolHTTP
                                       (SomeDomain (subdomain 21 22))
                                       (SomeInt 23)
                                       (url_path_res (anypath 24))))
                       (a!7 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 66)
                                                                   (url_path_data 67
                                                                                  68)))))
                       (a!8 (SomeHTMLElement (HTMLForm MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 60)
                                                                  (url_path_data 61
                                                                                 62)))))
                       (a!10 (DOMElementForm (Build_Form MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 60)
                                                                    (url_path_data 61
                                                                                   62)))))
                       (a!13 (Build_RequestHeaders
                               NoneOrigin
                               (Build_ArrayoptionCookieMapping
                                 NoneCookieMapping
                                 NoneCookieMapping
                                 NoneCookieMapping
                                 NoneCookieMapping
                                 NoneCookieMapping
                                 NoneCookieMapping)
                               NoneURL))
                       (a!14 (Build_URL ProtocolHTTP
                                        (SomeDomain (subdomain 30 31))
                                        (SomeInt 32)
                                        (url_path_res (anypath 33))))
                       (a!15 (SomeSetCookie (Build_SetCookie (NoPrefix 34)
                                                             35
                                                             NoneDomain
                                                             (subdomain 30 31)
                                                             (anypath 36)
                                                             false
                                                             false
                                                             SSStrict)))
                       (a!16 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                       (SomeoptionInt (SomeInt 37))
                                                       38
                                                       NoneInt
                                                       NonePath)))
                       (a!17 (SomeTrustedTypes (Build_TrustedTypes
                                                 (SomeoptionInt (SomeInt 39))
                                                 false)))
                       (a!19 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 46)
                                                                    (url_path_data 47
                                                                                   48)))))
                       (a!20 (SomeHTMLElement (HTMLForm MethodGet
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 49)
                                                                   (url_path_data 50
                                                                                  51)))))
                       (a!21 (SomeHTMLElement (HTMLForm MethodGet
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 52)
                                                                   (url_path_data 53
                                                                                  54)))))
                       (a!22 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 99)
                                                                    (url_path_data 100
                                                                                   101)))))
                       (a!23 (SomeHTMLElement (HTMLForm MethodGet
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 42)
                                                                   (url_path_data 43
                                                                                  44)))))
                       (a!29 (Build_ArrayoptionprodprodEmitterIntInt
                               NoneprodprodEmitterIntInt
                               (SomeprodprodEmitterIntInt
                                 (pairprodEmitterIntInt
                                   (pairEmitterInt EmitterClient 3)
                                   1))
                               (SomeprodprodEmitterIntInt
                                 (pairprodEmitterIntInt
                                   (pairEmitterInt EmitterClient 0)
                                   3))
                               NoneprodprodEmitterIntInt
                               NoneprodprodEmitterIntInt
                               NoneprodprodEmitterIntInt))
                       (a!31 (DOMElementForm (Build_Form MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 49)
                                                                    (url_path_data 50
                                                                                   51)))))
                       (a!32 (DOMElementForm (Build_Form MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 52)
                                                                    (url_path_data 53
                                                                                   54)))))
                       (a!33 (DOMElementForm (Build_Form MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 42)
                                                                    (url_path_data 43
                                                                                   44))))))
                 (let ((a!3 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                 (SomeoptionInt NoneInt)
                                                                 22
                                                                 NoneInt
                                                                 NonePath))
                                       a!2))
                       (a!9 (Build_HTML 58
                                        59
                                        (Build_ArrayoptionHTMLElement
                                          a!5
                                          (SomeHTMLElement (HTMLScript a!6))
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          a!7
                                          a!8)))
                       (a!18 (Build_ResponseHeaders
                               (SomeContentType ContentTypeHTML)
                               a!15
                               NoneOrigin
                               NoneURL
                               (SomeCSP (Build_CSP a!16 a!17))
                               NoneReferrerPolicy))
                       (a!24 (Build_HTML 40
                                         41
                                         (Build_ArrayoptionHTMLElement
                                           (SomeHTMLElement (HTMLFrame a!1))
                                           a!19
                                           a!20
                                           a!21
                                           a!22
                                           a!23)))
                       (a!26 (consEvent (EvRequest EmitterClient
                                                   (Build_Request MethodGet
                                                                  a!14
                                                                  a!13
                                                                  (SomeInt 79))
                                                   1)
                                        nilEvent)))
                 (let ((a!4 (Build_ResponseHeaders
                              (SomeContentType ContentTypeHTML)
                              NoneSetCookie
                              NoneOrigin
                              (SomeURL (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 120)
                                                  (url_path_data 121 122)))
                              (SomeCSP a!3)
                              NoneReferrerPolicy))
                       (a!25 (EvResponse (Build_Response a!14
                                                         ResponseOk
                                                         a!18
                                                         (SomeContentElement
                                                           (ContentElementHTML
                                                             a!24)))
                                         1))
                       (a!30 (SomeDOMElement (DOMElementResource
                                               a!1
                                               (ContentElementFrame
                                                 (Build_Frame a!1 2)
                                                 a!9)))))
                 (let ((a!11 (Build_Document 6
                                             2
                                             a!4
                                             a!9
                                             (Build_DOM 2
                                                        0
                                                        (Build_ArrayoptionDOMElement
                                                          NoneDOMElement
                                                          NoneDOMElement
                                                          NoneDOMElement
                                                          NoneDOMElement
                                                          NoneDOMElement
                                                          (SomeDOMElement a!10)))
                                             (Build_Initiators NoneInt
                                                               (Build_ArrayoptionInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt))))
                       (a!12 (Build_Response a!1
                                             ResponseOk
                                             a!4
                                             (SomeContentElement
                                               (ContentElementFrame
                                                 (Build_Frame a!1 2)
                                                 a!9))))
                       (a!27 (consEvent (EvRequest EmitterClient
                                                   (Build_Request MethodGet
                                                                  a!1
                                                                  a!13
                                                                  (SomeInt 73))
                                                   2)
                                        (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                         DOMTopLevel))
                                                   (consEvent a!25 a!26))))
                       (a!34 (Build_Document 6
                                             1
                                             a!18
                                             a!24
                                             (Build_DOM 1
                                                        0
                                                        (Build_ArrayoptionDOMElement
                                                          a!30
                                                          NoneDOMElement
                                                          (SomeDOMElement a!31)
                                                          (SomeDOMElement a!32)
                                                          NoneDOMElement
                                                          (SomeDOMElement a!33)))
                                             (Build_Initiators NoneInt
                                                               (Build_ArrayoptionInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt
                                                                 NoneInt)))))
                 (let ((a!28 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                              (DOMIndex 0)))
                                        (consEvent (EvResponse a!12 2) a!27)))
                       (a!35 (Build_State 6
                                          (Build_FetchEngine
                                            5
                                            EmitterClient
                                            (Build_Request MethodGet
                                                           a!1
                                                           a!13
                                                           (SomeInt 73))
                                            2
                                            (SomeResponse a!12)
                                            a!29)
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
                                                        a!14
                                                        NoneDomain
                                                        a!34)
                                          (Build_ArrayoptionSetCookie
                                            a!15
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
                   (=> (= (@2ArrayWindow (windows A))
                          (Build_Window 2 (SomeInt 3) a!1 NoneDomain a!11))
                       (Reachable A a!28 a!35)))))))
                 :weight 0))))
(let ((a!2 (hyper-res a!1
                      (forall ((A Global)
                               (B NestedDOMPath)
                               (C Bool)
                               (D Window)
                               (E Window)
                               (F Bool)
                               (G Bool)
                               (H Bool)
                               (I Bool)
                               (J Bool)
                               (K Bool)
                               (L Bool)
                               (M Bool))
                        (! (let ((a!1 (Build_RequestHeaders
                                        NoneOrigin
                                        (Build_ArrayoptionCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping)
                                        NoneURL))
                                 (a!4 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 21 22))
                                                 (SomeInt 23)
                                                 (url_path_res (anypath 24))))
                                 (a!6 (SomeTrustedTypes (Build_TrustedTypes
                                                          (SomeoptionInt (SomeInt 44301))
                                                          false)))
                                 (a!8 (SomeContentElement
                                        (ContentElementHTML
                                          (Build_HTML 44084
                                                      44085
                                                      (Build_ArrayoptionHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement)))))
                                 (a!9 (SomeTrustedTypes (Build_TrustedTypes
                                                          (SomeoptionInt (SomeInt 44102))
                                                          false)))
                                 (a!11 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 43892
                                                       43893
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!12 (Build_ResponseHeaders
                                         NoneContentType
                                         NoneSetCookie
                                         (SomeOrigin (OpaqueOrigin 24446))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 44453)
                                                             (url_path_data 44150
                                                                            44151)))
                                         (SomeCSP (Build_CSP NoneCSPSrc
                                                             NoneTrustedTypes))
                                         NoneReferrerPolicy))
                                 (a!13 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 44684
                                                       44685
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!14 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 44957
                                                       44958
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!16 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                                           (SomeTrustedTypes (Build_TrustedTypes
                                                                               NoneoptionInt
                                                                               false)))))
                                 (a!17 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 43688
                                                       43689
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!19 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            45106
                                                                            (SomeInt 48218)
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                 (a!23 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 47811)
                                                                               (url_path_data 45824
                                                                                              45825))
                                                                    44719)))
                                 (a!24 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 48088)
                                                                               (url_path_data 47622
                                                                                              47623))
                                                                    44503)))
                                 (a!25 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 45465)
                                                                              (url_path_data 45352
                                                                                             45353)))))
                                 (a!26 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 45172)
                                                                              (url_path_data 47480
                                                                                             47481)))))
                                 (a!27 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 46028)
                                                                              (url_path_data 47053
                                                                                             47054)))))
                                 (a!29 (Build_Document 7730
                                                       7731
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 7726
                                                                   7727
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 7728
                                                                  7729
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 32384)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 39765)
                                                                           (SomeInt 17617)
                                                                           (SomeInt 20802)
                                                                           (SomeInt 41888)
                                                                           (SomeInt 27332)
                                                                           (SomeInt 17658)))))
                                 (a!30 (Build_URL ProtocolHTTP
                                                  (SomeDomain (subdomain 30 31))
                                                  (SomeInt 32)
                                                  (url_path_res (anypath 45))))
                                 (a!31 (SomeTrustedTypes (Build_TrustedTypes
                                                           (SomeoptionInt (SomeInt 123))
                                                           false)))
                                 (a!34 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 63)
                                                                              (url_path_data 64
                                                                                             65)))))
                                 (a!35 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 66)
                                                                              (url_path_data 67
                                                                                             68)))))
                                 (a!36 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 60)
                                                                             (url_path_data 61
                                                                                            62)))))
                                 (a!38 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 60)
                                                                              (url_path_data 61
                                                                                             62)))))
                                 (a!42 (Build_Document 7737
                                                       7738
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 7733
                                                                   7734
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 7735
                                                                  7736
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 28151)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 42254)
                                                                           (SomeInt 30035)
                                                                           (SomeInt 41043)
                                                                           (SomeInt 20657)
                                                                           (SomeInt 29050)
                                                                           (SomeInt 14838)))))
                                 (a!43 (SomeTrustedTypes (Build_TrustedTypes
                                                           (SomeoptionInt (SomeInt 44806))
                                                           false)))
                                 (a!45 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 45956)
                                                                              (url_path_data 47334
                                                                                             47335)))))
                                 (a!46 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 47096)
                                                                              (url_path_data 45202
                                                                                             45203)))))
                                 (a!49 (Build_ArrayContentElement
                                         (ContentElementHTML
                                           (Build_HTML 14457
                                                       14458
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 28396
                                                       28397
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 30314
                                                       30315
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 14555
                                                       14556
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 19793
                                                       19794
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 16813
                                                       16814
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!51 (Build_URL ProtocolHTTP
                                                  (SomeDomain (subdomain 30 31))
                                                  (SomeInt 32)
                                                  (url_path_res (anypath 33))))
                                 (a!52 (SomeSetCookie (Build_SetCookie (NoPrefix 34)
                                                                       35
                                                                       NoneDomain
                                                                       (subdomain 30
                                                                                  31)
                                                                       (anypath 36)
                                                                       false
                                                                       false
                                                                       SSStrict)))
                                 (a!53 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                 (SomeoptionInt (SomeInt 37))
                                                                 38
                                                                 NoneInt
                                                                 NonePath)))
                                 (a!54 (SomeTrustedTypes (Build_TrustedTypes
                                                           (SomeoptionInt (SomeInt 39))
                                                           false)))
                                 (a!56 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 46)
                                                                              (url_path_data 47
                                                                                             48)))))
                                 (a!57 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 49)
                                                                             (url_path_data 50
                                                                                            51)))))
                                 (a!58 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 52)
                                                                             (url_path_data 53
                                                                                            54)))))
                                 (a!59 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 99)
                                                                              (url_path_data 100
                                                                                             101)))))
                                 (a!60 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 42)
                                                                             (url_path_data 43
                                                                                            44)))))
                                 (a!63 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 49)
                                                                              (url_path_data 50
                                                                                             51)))))
                                 (a!64 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 52)
                                                                              (url_path_data 53
                                                                                             54)))))
                                 (a!65 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 42)
                                                                              (url_path_data 43
                                                                                             44)))))
                                 (a!75 (Build_ArrayoptionprodprodEmitterIntInt
                                         NoneprodprodEmitterIntInt
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 3)
                                             1))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 0)
                                             3))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 4)
                                             2907))
                                         NoneprodprodEmitterIntInt
                                         NoneprodprodEmitterIntInt))
                                 (a!77 (SomeHTMLElement (HTMLScript (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 34063)
                                                                               (url_path_data 15847
                                                                                              15848)))))
                                 (a!96 (= (DOMPath (consInt 0 nilInt)
                                                   (DOMIndex 1))
                                          (DOMPath (consInt 0 nilInt)
                                                   (DOMIndex 1)))))
                           (let ((a!2 (Build_Request MethodGet
                                                     (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 30313)
                                                                (url_path_blob (OpaqueOrigin 25749)
                                                                               43362))
                                                     a!1
                                                     (SomeInt 40953)))
                                 (a!3 (Build_Request MethodGet
                                                     (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 28915)
                                                                (url_path_blob (OpaqueOrigin 37623)
                                                                               43363))
                                                     a!1
                                                     (SomeInt 34122)))
                                 (a!7 (Build_ResponseHeaders
                                        NoneContentType
                                        NoneSetCookie
                                        NoneOrigin
                                        (SomeURL (Build_URL ProtocolHTTP
                                                            NoneDomain
                                                            (SomeInt 44605)
                                                            (url_path_data 44635
                                                                           44636)))
                                        (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf)
                                                            a!6))
                                        NoneReferrerPolicy))
                                 (a!10 (Build_ResponseHeaders
                                         NoneContentType
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 43442)
                                                             (url_path_data 44817
                                                                            44818)))
                                         (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf)
                                                             a!9))
                                         NoneReferrerPolicy))
                                 (a!15 (Build_Response (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 24840)
                                                                  (url_path_data 16870
                                                                                 16871))
                                                       ResponseOk
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         (SomeOrigin (OpaqueOrigin 44343))
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       a!14))
                                 (a!18 (Build_Response (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 17786)
                                                                  (url_path_data 43173
                                                                                 43174))
                                                       ResponseOk
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         (SomeOrigin (OpaqueOrigin 44895))
                                                         NoneURL
                                                         a!16
                                                         NoneReferrerPolicy)
                                                       a!17))
                                 (a!20 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeScript)
                                         NoneSetCookie
                                         (SomeOrigin (OpaqueOrigin 35009))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 43925)
                                                             (url_path_data 44795
                                                                            44796)))
                                         (SomeCSP a!19)
                                         NoneReferrerPolicy))
                                 (a!28 (Build_Document 7723
                                                       7724
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 7719
                                                                   7720
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     a!25
                                                                     a!26
                                                                     a!27
                                                                     NoneHTMLElement))
                                                       (Build_DOM 7721
                                                                  7722
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 20478)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 18333)
                                                                           (SomeInt 22231)
                                                                           (SomeInt 19859)
                                                                           (SomeInt 37951)
                                                                           (SomeInt 28349)
                                                                           (SomeInt 38687)))))
                                 (a!32 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            (SomeoptionInt NoneInt)
                                                                            22
                                                                            NoneInt
                                                                            NonePath))
                                                  a!31))
                                 (a!37 (Build_HTML 58
                                                   59
                                                   (Build_ArrayoptionHTMLElement
                                                     a!34
                                                     (SomeHTMLElement (HTMLScript a!4))
                                                     NoneHTMLElement
                                                     NoneHTMLElement
                                                     a!35
                                                     a!36)))
                                 (a!40 (SomeDOMElement (DOMElementResource
                                                         a!4
                                                         (ContentElementScript
                                                           (Build_Script a!4 8)))))
                                 (a!44 (Build_ResponseHeaders
                                         NoneContentType
                                         NoneSetCookie
                                         NoneOrigin
                                         NoneURL
                                         (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf)
                                                             a!43))
                                         NoneReferrerPolicy))
                                 (a!55 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         a!52
                                         NoneOrigin
                                         NoneURL
                                         (SomeCSP (Build_CSP a!53 a!54))
                                         NoneReferrerPolicy))
                                 (a!61 (Build_HTML 40
                                                   41
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!30))
                                                     a!56
                                                     a!57
                                                     a!58
                                                     a!59
                                                     a!60)))
                                 (a!69 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!51
                                                                            a!1
                                                                            (SomeInt 79))
                                                             1)
                                                  nilEvent))
                                 (a!78 (Build_HTML 40
                                                   41
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!30))
                                                     a!56
                                                     a!57
                                                     a!77
                                                     a!59
                                                     a!60))))
                           (let ((a!5 (Build_ArrayRequest
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 15210)
                                                                  (url_path_res slash))
                                                       a!1
                                                       (SomeInt 29705))
                                        a!2
                                        a!3
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 14866)
                                                                  (url_path_data 23094
                                                                                 23095))
                                                       a!1
                                                       (SomeInt 18332))
                                        (Build_Request MethodGet
                                                       a!4
                                                       a!1
                                                       (SomeInt 29839))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 15184)
                                                                  (url_path_data 36106
                                                                                 36107))
                                                       a!1
                                                       (SomeInt 24970))))
                                 (a!21 (Build_Response a!4
                                                       ResponseOk
                                                       a!20
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!4 8)))))
                                 (a!33 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 120)
                                                             (url_path_data 121
                                                                            122)))
                                         (SomeCSP a!32)
                                         NoneReferrerPolicy))
                                 (a!47 (Build_Document 7744
                                                       7745
                                                       a!44
                                                       (Build_HTML 7740
                                                                   7741
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     a!45
                                                                     NoneHTMLElement
                                                                     a!46
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 7742
                                                                  7743
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 25006)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 15925)
                                                                           (SomeInt 22037)
                                                                           (SomeInt 34024)
                                                                           (SomeInt 38965)
                                                                           (SomeInt 40432)
                                                                           (SomeInt 19642)))))
                                 (a!62 (SomeDOMElement (DOMElementResource
                                                         a!4
                                                         (ContentElementFrame
                                                           (Build_Frame a!30 3)
                                                           a!37))))
                                 (a!68 (EvResponse (Build_Response a!51
                                                                   ResponseOk
                                                                   a!55
                                                                   (SomeContentElement
                                                                     (ContentElementHTML
                                                                       a!61)))
                                                   1)))
                           (let ((a!22 (Build_ArrayResponse
                                         (Build_Response (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 25938)
                                                                    (url_path_data 33837
                                                                                   33838))
                                                         ResponseOk
                                                         a!7
                                                         a!8)
                                         (Build_Response (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 35448)
                                                                    (url_path_data 33648
                                                                                   33649))
                                                         ResponseOk
                                                         a!10
                                                         a!11)
                                         (Build_Response (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 19154)
                                                                    (url_path_data 33379
                                                                                   33380))
                                                         ResponseOk
                                                         a!12
                                                         a!13)
                                         a!15
                                         a!18
                                         a!21))
                                 (a!39 (Build_Document 6
                                                       2
                                                       a!33
                                                       a!37
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!38)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!41 (Build_Document 9
                                                       2
                                                       a!33
                                                       a!37
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    a!40
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!38)))
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
                                                       a!55
                                                       a!61
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!62
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!63)
                                                                    (SomeDOMElement a!64)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!65)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!67 (Build_Response a!30
                                                       ResponseOk
                                                       a!33
                                                       (SomeContentElement
                                                         (ContentElementFrame
                                                           (Build_Frame a!30 2)
                                                           a!37))))
                                 (a!70 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!30
                                                                            a!1
                                                                            (SomeInt 73))
                                                             2)
                                                  (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                                   DOMTopLevel))
                                                             (consEvent a!68
                                                                        a!69))))
                                 (a!76 (Build_FetchEngine
                                         8
                                         EmitterClient
                                         (Build_Request MethodGet
                                                        a!4
                                                        a!1
                                                        (SomeInt 29839))
                                         3
                                         (SomeResponse a!21)
                                         a!75))
                                 (a!79 (Build_Document 10
                                                       1
                                                       a!55
                                                       a!78
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!62
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!63)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!65)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt)))))
                           (let ((a!48 (Build_ArrayWindow
                                         (Build_Window 7725
                                                       (SomeInt 42942)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 20609)
                                                                  (url_path_data 39154
                                                                                 39155))
                                                       NoneDomain
                                                       a!28)
                                         (Build_Window 7732
                                                       (SomeInt 17752)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 31553)
                                                                  (url_path_data 23499
                                                                                 23500))
                                                       NoneDomain
                                                       a!29)
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!30
                                                       NoneDomain
                                                       a!39)
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!30
                                                       NoneDomain
                                                       a!41)
                                         (Build_Window 7739
                                                       (SomeInt 39720)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 37442)
                                                                  (url_path_data 14674
                                                                                 14675))
                                                       NoneDomain
                                                       a!42)
                                         (Build_Window 7746
                                                       (SomeInt 16668)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 18668)
                                                                  (url_path_data 22120
                                                                                 22121))
                                                       NoneDomain
                                                       a!47)))
                                 (a!71 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                        (DOMIndex 0)))
                                                  (consEvent (EvResponse a!67 2)
                                                             a!70)))
                                 (a!80 (Build_State 10
                                                    a!76
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
                                                                  a!51
                                                                  NoneDomain
                                                                  a!79)
                                                    (Build_ArrayoptionSetCookie
                                                      a!52
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
                                 (a!83 (dm_body (dc_dom (wd_document (Build_Window 1
                                                                                   NoneInt
                                                                                   a!51
                                                                                   NoneDomain
                                                                                   a!79)))))
                                 (a!90 (= (Build_Window 2
                                                        (SomeInt 3)
                                                        a!30
                                                        NoneDomain
                                                        a!41)
                                          (Build_Window 2
                                                        (SomeInt 3)
                                                        a!30
                                                        NoneDomain
                                                        a!41)))
                                 (a!109 (dc_dom (wd_document (Build_Window 2
                                                                           (SomeInt 3)
                                                                           a!30
                                                                           NoneDomain
                                                                           a!41)))))
                           (let ((a!50 (Build_Global a!5
                                                     a!22
                                                     (Build_ArrayInt 7713
                                                                     7714
                                                                     7715
                                                                     7716
                                                                     7717
                                                                     7718)
                                                     (Build_ArrayEmitter
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       a!23
                                                       a!24)
                                                     a!48
                                                     a!49
                                                     (Build_ArrayprodOriginoptionCSP
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 26837)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 39319)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 24555)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 15277)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 41299)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 17423)
                                                         NoneCSP))
                                                     (Build_Config false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   true
                                                                   false
                                                                   false
                                                                   false
                                                                   false)))
                                 (a!72 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!4
                                                                            a!1
                                                                            (SomeInt 29839))
                                                             3)
                                                  a!71))
                                 (a!81 (rp_hd_csp (dc_headers (wd_document (st_window a!80)))))
                                 (a!84 (ite (= 0 2)
                                            (@2ArrayoptionDOMElement a!83)
                                            (ite (= 0 3)
                                                 (@3ArrayoptionDOMElement a!83)
                                                 (ite (= 0 4)
                                                      (@4ArrayoptionDOMElement
                                                        a!83)
                                                      (@defaultArrayoptionDOMElement
                                                        a!83)))))
                                 (a!99 ((_ is ProtocolHTTPS)
                                         (url_protocol (wd_location (st_window a!80)))))
                                 (a!100 ((_ is ProtocolHTTP)
                                          (url_protocol (wd_location (st_window a!80)))))
                                 (a!101 (TupleOrigin (url_protocol (wd_location (st_window a!80)))
                                                     (url_host (wd_location (st_window a!80)))
                                                     (url_port (wd_location (st_window a!80)))))
                                 (a!102 ((_ is ProtocolData)
                                          (url_protocol (wd_location (st_window a!80)))))
                                 (a!103 ((_ is url_path_data)
                                          (url_path (wd_location (st_window a!80)))))
                                 (a!104 (@0url_path_data (url_path (wd_location (st_window a!80)))))
                                 (a!105 ((_ is url_path_blob)
                                          (url_path (wd_location (st_window a!80)))))
                                 (a!106 (@0url_path_blob (url_path (wd_location (st_window a!80)))))
                                 (a!110 (ite (= 1 3)
                                             (@3ArrayoptionDOMElement
                                               (dm_body a!109))
                                             (ite (= 1 4)
                                                  (@4ArrayoptionDOMElement
                                                    (dm_body a!109))
                                                  (@defaultArrayoptionDOMElement
                                                    (dm_body a!109))))))
                           (let ((a!73 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                                 nilInt)
                                                                        (DOMIndex 1)))
                                                  (consEvent (EvResponse a!21 3)
                                                             a!72)))
                                 (a!82 (and (= D E)
                                            (= (Build_Window 2
                                                             (SomeInt 3)
                                                             a!30
                                                             NoneDomain
                                                             a!41)
                                               D)
                                            (= (st_window a!80) E)
                                            (= B (DOMPath nilInt DOMTopLevel))
                                            (= (DOMPath (consInt 0 nilInt)
                                                        (DOMIndex 1))
                                               B)
                                            (= a!50 A)))
                                 (a!85 (ite (= 0 0)
                                            (@0ArrayoptionDOMElement a!83)
                                            (ite (= 0 1)
                                                 (@1ArrayoptionDOMElement a!83)
                                                 a!84)))
                                 (a!91 (ite (= (frame_window (Build_Frame a!30
                                                                          3))
                                               4)
                                            (@4ArrayWindow (windows a!50))
                                            (@defaultArrayWindow (windows a!50))))
                                 (a!98 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))
                                          CSPSrcSelf))
                                 (a!107 (ite a!102
                                             (ite a!103
                                                  (SomeOrigin (OpaqueOrigin a!104))
                                                  NoneOrigin)
                                             (ite a!103
                                                  NoneOrigin
                                                  (ite a!105
                                                       (SomeOrigin a!106)
                                                       NoneOrigin))))
                                 (a!111 (ite (= 1 1)
                                             (@1ArrayoptionDOMElement
                                               (dm_body a!109))
                                             (ite (= 1 2)
                                                  (@2ArrayoptionDOMElement
                                                    (dm_body a!109))
                                                  a!110)))
                                 (a!120 (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))))
                                 (a!122 (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))))
                                 (a!123 (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))))
                                 (a!124 (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))))
                                 (a!125 (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))))
                                 (a!126 (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81))))))
                           (let ((a!74 (consEvent (EvScriptUpdateHTML
                                                    (DOMPath (consInt 0 nilInt)
                                                             (DOMIndex 1))
                                                    (DOMPath nilInt
                                                             (DOMIndex 3))
                                                    (Build_Window 1
                                                                  NoneInt
                                                                  a!51
                                                                  NoneDomain
                                                                  a!66))
                                                  a!73))
                                 (a!86 (= (@0SomeDOMElement a!85)
                                          (DOMElementResource
                                            (@0DOMElementResource
                                              (@0SomeDOMElement a!85))
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!85)))))
                                 (a!87 (ContentElementFrame
                                         (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!85)))
                                         (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!85)))))
                                 (a!88 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!85)))
                                          (Build_Frame a!30 3)))
                                 (a!89 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!85)))
                                          a!37))
                                 (a!92 (ite (= (frame_window (Build_Frame a!30
                                                                          3))
                                               3)
                                            (@3ArrayWindow (windows a!50))
                                            a!91))
                                 (a!108 (SomeOrigin (@0SomeOrigin (ite (or a!99
                                                                           a!100)
                                                                       (SomeOrigin a!101)
                                                                       a!107))))
                                 (a!112 (@0SomeDOMElement (ite (= 1 0)
                                                               (@0ArrayoptionDOMElement
                                                                 (dm_body a!109))
                                                               a!111)))
                                 (a!121 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))
                                           (CSPSrcScheme a!120)))
                                 (a!127 (= (@0SomeCSPSrc (csp_script_src (@0SomeCSP a!81)))
                                           (CSPSrcSource a!122
                                                         a!123
                                                         a!124
                                                         a!125
                                                         a!126)))
                                 (a!133 (not (= a!125
                                                (SomeInt (@0SomeInt a!125)))))
                                 (a!135 (not (= a!122
                                                (SomeProtocol (@0SomeProtocol a!122)))))
                                 (a!137 (not (= a!126
                                                (SomePath (@0SomePath a!126)))))
                                 (a!140 (not (= a!123
                                                (SomeoptionInt (@0SomeoptionInt a!123)))))
                                 (a!142 (= (@0SomeoptionInt a!123)
                                           (SomeInt (@0SomeInt (@0SomeoptionInt a!123)))))
                                 (a!147 ((_ is SomeDOMElement)
                                          (ite (= 1 0)
                                               (@0ArrayoptionDOMElement
                                                 (dm_body a!109))
                                               a!111))))
                           (let ((a!93 (ite (= (frame_window (Build_Frame a!30
                                                                          3))
                                               2)
                                            (@2ArrayWindow (windows a!50))
                                            a!92))
                                 (a!113 (url_protocol (script_src (@0ContentElementScript
                                                                    (@1DOMElementResource
                                                                      a!112)))))
                                 (a!114 (url_host (script_src (@0ContentElementScript
                                                                (@1DOMElementResource
                                                                  a!112)))))
                                 (a!115 (url_port (script_src (@0ContentElementScript
                                                                (@1DOMElementResource
                                                                  a!112)))))
                                 (a!116 (url_path (script_src (@0ContentElementScript
                                                                (@1DOMElementResource
                                                                  a!112))))))
                           (let ((a!94 (ite (= (frame_window (Build_Frame a!30
                                                                          3))
                                               1)
                                            (@1ArrayWindow (windows a!50))
                                            a!93))
                                 (a!117 (ite ((_ is url_path_data) a!116)
                                             (SomeOrigin (OpaqueOrigin (@0url_path_data a!116)))
                                             NoneOrigin))
                                 (a!118 (ite ((_ is url_path_data) a!116)
                                             NoneOrigin
                                             (ite ((_ is url_path_blob) a!116)
                                                  (SomeOrigin (@0url_path_blob a!116))
                                                  NoneOrigin)))
                                 (a!128 (not (= a!114
                                                (SomeDomain (@0SomeDomain a!114)))))
                                 (a!129 (not (= (@0domain (@0SomeDomain a!114))
                                                a!124)))
                                 (a!130 (= (@0SomeDomain a!114)
                                           (domain (@0domain (@0SomeDomain a!114)))))
                                 (a!131 (not (= (@1subdomain (@0SomeDomain a!114))
                                                a!124)))
                                 (a!132 (= (@0SomeDomain a!114)
                                           (subdomain (@0subdomain (@0SomeDomain a!114))
                                                      (@1subdomain (@0SomeDomain a!114)))))
                                 (a!134 (not (= a!115
                                                (SomeInt (@0SomeInt a!125)))))
                                 (a!136 (or a!135
                                            (not (= a!113
                                                    (@0SomeProtocol a!122)))))
                                 (a!138 (not (= a!116
                                                (url_path_res (@0url_path_res a!116)))))
                                 (a!143 (not (= (@0subdomain (@0SomeDomain a!114))
                                                (@0SomeInt (@0SomeoptionInt a!123))))))
                           (let ((a!95 (ite (= (frame_window (Build_Frame a!30
                                                                          3))
                                               0)
                                            (@0ArrayWindow (windows a!50))
                                            a!94))
                                 (a!119 (= a!108
                                           (ite (or ((_ is ProtocolHTTPS) a!113)
                                                    ((_ is ProtocolHTTP) a!113))
                                                (SomeOrigin (TupleOrigin a!113
                                                                         a!114
                                                                         a!115))
                                                (ite ((_ is ProtocolData) a!113)
                                                     a!117
                                                     a!118))))
                                 (a!139 (or a!137
                                            a!138
                                            (not (= (@0url_path_res a!116)
                                                    (@0SomePath a!126)))))
                                 (a!141 (or (not (= (@0SomeoptionInt a!123)
                                                    NoneInt))
                                            a!128
                                            (not a!132))))
                           (let ((a!97 (and (= a!85
                                               (SomeDOMElement (@0SomeDOMElement a!85)))
                                            a!86
                                            (= (@1DOMElementResource
                                                 (@0SomeDOMElement a!85))
                                               a!87)
                                            a!88
                                            a!89
                                            a!90
                                            a!90
                                            a!90
                                            a!90
                                            (= (st_window a!80)
                                               (Build_Window 1
                                                             NoneInt
                                                             a!51
                                                             NoneDomain
                                                             a!79))
                                            (= a!95
                                               (Build_Window 2
                                                             (SomeInt 3)
                                                             a!30
                                                             NoneDomain
                                                             a!41))
                                            a!96
                                            (= (DOMPath nilInt (DOMIndex 1))
                                               (DOMPath nilInt (DOMIndex 1)))
                                            (= (DOMPath nilInt (DOMIndex 1))
                                               (DOMPath nilInt (DOMIndex 1)))
                                            a!96
                                            (= a!50 a!50)
                                            (= a!50 a!50)))
                                 (a!144 (or a!140
                                            (and a!141
                                                 (or (not a!142)
                                                     a!128
                                                     (not a!132)
                                                     a!143)))))
                           (let ((a!145 (and a!144
                                             (or (not (= a!123 NoneoptionInt))
                                                 a!128
                                                 (not a!130)))))
                           (let ((a!146 (or (not a!127)
                                            a!128
                                            (and (or a!129 (not a!130))
                                                 (or a!131 (not a!132)))
                                            (and (or a!133 a!134)
                                                 (not (= a!125 NoneInt)))
                                            (and a!136
                                                 (not (= a!122 NoneProtocol)))
                                            (and a!139 (not (= a!126 NonePath)))
                                            a!145)))
                           (let ((a!148 (and (Reachable a!50 a!74 a!80)
                                             ((_ is SomeCSPSrc)
                                               (csp_script_src (@0SomeCSP a!81)))
                                             (or a!82 a!97)
                                             (or (not a!98) (not a!119))
                                             (or (not a!121)
                                                 (not (= a!113 a!120)))
                                             a!146
                                             ((_ is SomeOrigin)
                                               (ite (or a!99 a!100)
                                                    (SomeOrigin a!101)
                                                    a!107))
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource a!112))
                                             (= a!74 a!74)
                                             a!147
                                             ((_ is DOMElementResource) a!112)
                                             ((_ is SomeCSP) a!81)
                                             ((_ is Build_CSP) (@0SomeCSP a!81)))))
                             (=> a!148 (query!0 a!80 a!74 a!50)))))))))))))))))
                           :weight 0))))
      (a!5 (Build_Request MethodGet
                          (Build_URL ProtocolHTTP
                                     NoneDomain
                                     (SomeInt 30313)
                                     (url_path_blob (OpaqueOrigin 25749) 43362))
                          a!4
                          (SomeInt 40953)))
      (a!6 (Build_Request MethodGet
                          (Build_URL ProtocolHTTP
                                     NoneDomain
                                     (SomeInt 28915)
                                     (url_path_blob (OpaqueOrigin 37623) 43363))
                          a!4
                          (SomeInt 34122)))
      (a!10 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 44605)
                                  (url_path_data 44635 44636)))
              (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf) a!9))
              NoneReferrerPolicy))
      (a!13 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 43442)
                                  (url_path_data 44817 44818)))
              (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf) a!12))
              NoneReferrerPolicy))
      (a!18 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 24840)
                                       (url_path_data 16870 16871))
                            ResponseOk
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              (SomeOrigin (OpaqueOrigin 44343))
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            a!17))
      (a!21 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 17786)
                                       (url_path_data 43173 43174))
                            ResponseOk
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              (SomeOrigin (OpaqueOrigin 44895))
                              NoneURL
                              a!19
                              NoneReferrerPolicy)
                            a!20))
      (a!23 (Build_ResponseHeaders
              (SomeContentType ContentTypeScript)
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 35009))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 43925)
                                  (url_path_data 44795 44796)))
              (SomeCSP a!22)
              NoneReferrerPolicy))
      (a!31 (Build_Document 7723
                            7724
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 7719
                                        7720
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          a!28
                                          a!29
                                          a!30
                                          NoneHTMLElement))
                            (Build_DOM 7721
                                       7722
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 20478)
                                              (Build_ArrayoptionInt
                                                (SomeInt 18333)
                                                (SomeInt 22231)
                                                (SomeInt 19859)
                                                (SomeInt 37951)
                                                (SomeInt 28349)
                                                (SomeInt 38687)))))
      (a!35 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 (SomeoptionInt NoneInt)
                                                 22
                                                 NoneInt
                                                 NonePath))
                       a!34))
      (a!40 (Build_HTML 58
                        59
                        (Build_ArrayoptionHTMLElement
                          a!37
                          (SomeHTMLElement (HTMLScript a!7))
                          NoneHTMLElement
                          NoneHTMLElement
                          a!38
                          a!39)))
      (a!43 (SomeDOMElement (DOMElementResource
                              a!7
                              (ContentElementScript (Build_Script a!7 8)))))
      (a!47 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              NoneOrigin
              NoneURL
              (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcSelf) a!46))
              NoneReferrerPolicy))
      (a!59 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              a!56
              NoneOrigin
              NoneURL
              (SomeCSP (Build_CSP a!57 a!58))
              NoneReferrerPolicy))
      (a!65 (Build_HTML 40
                        41
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!33))
                          a!60
                          a!61
                          a!62
                          a!63
                          a!64)))
      (a!67 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!55
                                                 a!4
                                                 (SomeInt 79))
                                  1)
                       nilEvent))
      (a!81 (Build_HTML 40
                        41
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!33))
                          a!60
                          a!61
                          a!80
                          a!63
                          a!64))))
(let ((a!8 (Build_ArrayRequest
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 15210)
                                       (url_path_res slash))
                            a!4
                            (SomeInt 29705))
             a!5
             a!6
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 14866)
                                       (url_path_data 23094 23095))
                            a!4
                            (SomeInt 18332))
             (Build_Request MethodGet a!7 a!4 (SomeInt 29839))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 15184)
                                       (url_path_data 36106 36107))
                            a!4
                            (SomeInt 24970))))
      (a!24 (Build_Response a!7
                            ResponseOk
                            a!23
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!7 8)))))
      (a!36 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 120)
                                  (url_path_data 121 122)))
              (SomeCSP a!35)
              NoneReferrerPolicy))
      (a!50 (Build_Document 7744
                            7745
                            a!47
                            (Build_HTML 7740
                                        7741
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          a!48
                                          NoneHTMLElement
                                          a!49
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 7742
                                       7743
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 25006)
                                              (Build_ArrayoptionInt
                                                (SomeInt 15925)
                                                (SomeInt 22037)
                                                (SomeInt 34024)
                                                (SomeInt 38965)
                                                (SomeInt 40432)
                                                (SomeInt 19642)))))
      (a!66 (EvResponse (Build_Response a!55
                                        ResponseOk
                                        a!59
                                        (SomeContentElement
                                          (ContentElementHTML a!65)))
                        1))
      (a!74 (SomeDOMElement (DOMElementResource
                              a!7
                              (ContentElementFrame (Build_Frame a!33 3) a!40))))
      (a!86 (SomeDOMElement (DOMElementResource
                              a!33
                              (ContentElementFrame (Build_Frame a!33 2) a!40)))))
(let ((a!25 (Build_ArrayResponse
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 25938)
                                         (url_path_data 33837 33838))
                              ResponseOk
                              a!10
                              a!11)
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 35448)
                                         (url_path_data 33648 33649))
                              ResponseOk
                              a!13
                              a!14)
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 19154)
                                         (url_path_data 33379 33380))
                              ResponseOk
                              a!15
                              a!16)
              a!18
              a!21
              a!24))
      (a!42 (Build_Document 6
                            2
                            a!36
                            a!40
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!41)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!44 (Build_Document 9
                            2
                            a!36
                            a!40
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         a!43
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!41)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!54 (Build_Response a!33
                            ResponseOk
                            a!36
                            (SomeContentElement
                              (ContentElementFrame (Build_Frame a!33 2) a!40))))
      (a!68 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!33
                                                 a!4
                                                 (SomeInt 73))
                                  2)
                       (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                  (consEvent a!66 a!67))))
      (a!73 (Build_FetchEngine
              8
              EmitterClient
              (Build_Request MethodGet a!7 a!4 (SomeInt 29839))
              3
              (SomeResponse a!24)
              a!72))
      (a!78 (Build_Document 9
                            1
                            a!59
                            a!65
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!74
                                         NoneDOMElement
                                         (SomeDOMElement a!75)
                                         (SomeDOMElement a!76)
                                         NoneDOMElement
                                         (SomeDOMElement a!77)))
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
                            a!59
                            a!81
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!74
                                         NoneDOMElement
                                         (SomeDOMElement a!75)
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!77)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!87 (Build_Document 6
                            1
                            a!59
                            a!65
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!86
                                         NoneDOMElement
                                         (SomeDOMElement a!75)
                                         (SomeDOMElement a!76)
                                         NoneDOMElement
                                         (SomeDOMElement a!77)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt)))))
(let ((a!51 (Build_ArrayWindow
              (Build_Window 7725
                            (SomeInt 42942)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 20609)
                                       (url_path_data 39154 39155))
                            NoneDomain
                            a!31)
              (Build_Window 7732
                            (SomeInt 17752)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 31553)
                                       (url_path_data 23499 23500))
                            NoneDomain
                            a!32)
              (Build_Window 2 (SomeInt 3) a!33 NoneDomain a!42)
              (Build_Window 2 (SomeInt 3) a!33 NoneDomain a!44)
              (Build_Window 7739
                            (SomeInt 39720)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 37442)
                                       (url_path_data 14674 14675))
                            NoneDomain
                            a!45)
              (Build_Window 7746
                            (SomeInt 16668)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 18668)
                                       (url_path_data 22120 22121))
                            NoneDomain
                            a!50)))
      (a!69 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 0)))
                       (consEvent (EvResponse a!54 2) a!68)))
      (a!83 (Build_State 10
                         a!73
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!55 NoneDomain a!82)
                         (Build_ArrayoptionSetCookie
                           a!56
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
      (a!92 (Build_State 7
                         (Build_FetchEngine
                           7
                           EmitterClient
                           (Build_Request MethodGet a!7 a!4 (SomeInt 29839))
                           3
                           NoneResponse
                           a!91)
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!55 NoneDomain a!87)
                         (Build_ArrayoptionSetCookie
                           a!56
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
      (a!94 (Build_State 6
                         (Build_FetchEngine
                           5
                           EmitterClient
                           (Build_Request MethodGet a!33 a!4 (SomeInt 73))
                           2
                           (SomeResponse a!54)
                           a!91)
                         (Build_ServiceWorker
                           0
                           (Build_ArrayoptionInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt
                             NoneInt))
                         (Build_Window 1 NoneInt a!55 NoneDomain a!87)
                         (Build_ArrayoptionSetCookie
                           a!56
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
(let ((a!53 (Build_Global a!8
                          a!25
                          (Build_ArrayInt 7713 7714 7715 7716 7717 7718)
                          (Build_ArrayEmitter
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            a!26
                            a!27)
                          a!51
                          a!52
                          (Build_ArrayprodOriginoptionCSP
                            (pairOriginoptionCSP (OpaqueOrigin 26837) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 39319) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 24555) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 15277) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 41299) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 17423) NoneCSP))
                          (Build_Config false
                                        false
                                        false
                                        false
                                        false
                                        false
                                        false
                                        true
                                        false
                                        false
                                        false
                                        false)))
      (a!70 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!7
                                                 a!4
                                                 (SomeInt 29839))
                                  3)
                       a!69)))
(let ((a!71 (consEvent (EvDOMUpdate (DOMPath (consInt 0 nilInt) (DOMIndex 1)))
                       (consEvent (EvResponse a!24 3) a!70)))
      (a!88 (Reachable a!53
                       (consEvent (EvResponse a!24 3) a!70)
                       (Build_State 8
                                    a!73
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
                                                  a!55
                                                  NoneDomain
                                                  a!87)
                                    (Build_ArrayoptionSetCookie
                                      a!56
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
                                      NoneStorageItem)))))
(let ((a!79 (Reachable a!53
                       a!71
                       (Build_State 9
                                    a!73
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
                                                  a!55
                                                  NoneDomain
                                                  a!78)
                                    (Build_ArrayoptionSetCookie
                                      a!56
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
      (a!84 (consEvent (EvScriptUpdateHTML
                         (DOMPath (consInt 0 nilInt) (DOMIndex 1))
                         (DOMPath nilInt (DOMIndex 3))
                         (Build_Window 1 NoneInt a!55 NoneDomain a!78))
                       a!71)))
(let ((a!89 (hyper-res (hyper-res a!2 a!3 (=> a!79 (query!0 a!83 a!84 a!53)))
                       a!85
                       (=> a!88 (query!0 a!83 a!84 a!53)))))
(let ((a!95 (hyper-res (hyper-res a!89
                                  a!90
                                  (=> (Reachable a!53 a!70 a!92)
                                      (query!0 a!83 a!84 a!53)))
                       a!93
                       (=> (Reachable a!53 a!69 a!94) (query!0 a!83 a!84 a!53)))))
  (hyper-res a!95 (asserted a!96) (query!0 a!83 a!84 a!53))))))))))))
