
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
                              (Q NestedDOMPath)
                              (R DOMSelector)
                              (S Window)
                              (T Window)
                              (U Global)
                              (V Window)
                              (W listEvent)
                              (X listInt)
                              (Y Int)
                              (Z Response)
                              (A1 Request)
                              (B1 Int)
                              (C1 Frame)
                              (D1 URL)
                              (E1 listEvent)
                              (F1 listEvent)
                              (G1 State))
                       (! (let ((a!1 (consEvent (EvDOMUpdate (DOMPath X
                                                                      (DOMIndex Y)))
                                                W))
                                (a!2 (@0ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!3 (@1ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!4 (@2ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!5 (@3ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!6 (@4ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!7 (@5ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!8 (@6ArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!9 (@defaultArrayoptionDOMElement
                                       (dm_body (dc_dom (wd_document V)))))
                                (a!20 (@0ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!21 (@1ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!22 (@2ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!23 (@3ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!24 (@4ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!25 (@5ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!26 (@6ArrayoptionInt (in_body (dc_init (wd_document V)))))
                                (a!27 (@defaultArrayoptionInt
                                        (in_body (dc_init (wd_document V)))))
                                (a!45 (and (= S T)
                                           (= V S)
                                           (= (st_window G1) T)
                                           (= Q (DOMPath nilInt R))
                                           (= (DOMPath X (DOMIndex Y)) Q)
                                           (= U P)))
                                (a!46 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!47 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!48 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!49 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!50 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!51 (@5ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!52 (@6ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!53 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!58 (ite (= (frame_window E) 5)
                                           (@5ArrayWindow (windows J))
                                           (ite (= (frame_window E) 6)
                                                (@6ArrayWindow (windows J))
                                                (@defaultArrayWindow
                                                  (windows J)))))
                                (a!63 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                       (DOMIndex 1)))
                                                 E1)))
                          (let ((a!10 (ite (= Y 4)
                                           a!6
                                           (ite (= Y 5)
                                                a!7
                                                (ite (= Y 6) a!8 a!9))))
                                (a!28 (ite (= Y 4)
                                           a!24
                                           (ite (= Y 5)
                                                a!25
                                                (ite (= Y 6) a!26 a!27))))
                                (a!54 (ite (= B 4)
                                           a!50
                                           (ite (= B 5)
                                                a!51
                                                (ite (= B 6) a!52 a!53))))
                                (a!59 (ite (= (frame_window E) 3)
                                           (@3ArrayWindow (windows J))
                                           (ite (= (frame_window E) 4)
                                                (@4ArrayWindow (windows J))
                                                a!58)))
                                (a!64 (consEvent (EvScriptCreateBlobUrl
                                                   (DOMPath nilInt (DOMIndex 1))
                                                   D1)
                                                 a!63)))
                          (let ((a!11 (ite (= Y 1)
                                           a!3
                                           (ite (= Y 2)
                                                a!4
                                                (ite (= Y 3) a!5 a!10))))
                                (a!29 (ite (= Y 1)
                                           a!21
                                           (ite (= Y 2)
                                                a!22
                                                (ite (= Y 3) a!23 a!28))))
                                (a!55 (ite (= B 1)
                                           a!47
                                           (ite (= B 2)
                                                a!48
                                                (ite (= B 3) a!49 a!54))))
                                (a!60 (ite (= (frame_window E) 1)
                                           (@1ArrayWindow (windows J))
                                           (ite (= (frame_window E) 2)
                                                (@2ArrayWindow (windows J))
                                                a!59)))
                                (a!65 (consEvent (EvScriptNavigateFrame
                                                   (DOMPath (consInt 0 nilInt)
                                                            (DOMIndex 1))
                                                   (DOMPath nilInt (DOMIndex 0))
                                                   C1
                                                   D1)
                                                 a!64)))
                          (let ((a!12 (@1DOMElementResource
                                        (@0SomeDOMElement (ite (= Y 0) a!2 a!11))))
                                (a!30 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 0))
                                (a!31 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 1))
                                (a!32 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 2))
                                (a!33 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 3))
                                (a!34 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 4))
                                (a!35 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 5))
                                (a!36 (= (@0SomeInt (ite (= Y 0) a!20 a!29)) 6))
                                (a!44 ((_ is DOMElementForm)
                                        (@0SomeDOMElement (ite (= Y 0) a!2 a!11))))
                                (a!56 (@1DOMElementResource
                                        (@0SomeDOMElement (ite (= B 0)
                                                               a!46
                                                               a!55))))
                                (a!57 ((_ is DOMElementForm)
                                        (@0SomeDOMElement (ite (= B 0)
                                                               a!46
                                                               a!55))))
                                (a!61 (= (ite (= (frame_window E) 0)
                                              (@0ArrayWindow (windows J))
                                              a!60)
                                         H))
                                (a!66 (consEvent (EvDOMUpdate (DOMPath X
                                                                       (DOMIndex Y)))
                                                 (consEvent (EvResponse Z B1)
                                                            (consEvent (EvRequest EmitterClient
                                                                                  A1
                                                                                  B1)
                                                                       a!65)))))
                          (let ((a!13 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              6)
                                           (@6ArrayWindow (windows U))
                                           (@defaultArrayWindow (windows U))))
                                (a!37 (ite a!35
                                           (@5ArrayWindow (windows U))
                                           (ite a!36
                                                (@6ArrayWindow (windows U))
                                                (@defaultArrayWindow
                                                  (windows U)))))
                                (a!62 (and (= (@0ContentElementFrame a!56) E)
                                           (= (@1ContentElementFrame a!56) D)
                                           (not ((_ is ContentElementScript)
                                                  a!56))
                                           (not ((_ is ContentElementImage)
                                                  a!56))
                                           (not ((_ is ContentElementHTML) a!56))
                                           (not a!57)
                                           ((_ is SomeDOMElement)
                                             (ite (= B 0) a!46 a!55))
                                           (= H O)
                                           (= N O)
                                           (= I N)
                                           (= V I)
                                           a!61
                                           (= (st_window G1) C)
                                           (= L (DOMPath F G))
                                           (= L (DOMPath nilInt M))
                                           (= A (DOMPath (consInt B F) G))
                                           (= (DOMPath X (DOMIndex Y)) A)
                                           (= U J)
                                           (= J K))))
                          (let ((a!14 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              5)
                                           (@5ArrayWindow (windows U))
                                           a!13))
                                (a!38 (ite a!33
                                           (@3ArrayWindow (windows U))
                                           (ite a!34
                                                (@4ArrayWindow (windows U))
                                                a!37))))
                          (let ((a!15 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              4)
                                           (@4ArrayWindow (windows U))
                                           a!14))
                                (a!39 (ite a!31
                                           (@1ArrayWindow (windows U))
                                           (ite a!32
                                                (@2ArrayWindow (windows U))
                                                a!38))))
                          (let ((a!16 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              3)
                                           (@3ArrayWindow (windows U))
                                           a!15))
                                (a!40 (wd_document (ite a!30
                                                        (@0ArrayWindow (windows U))
                                                        a!39))))
                          (let ((a!17 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              2)
                                           (@2ArrayWindow (windows U))
                                           a!16)))
                          (let ((a!18 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              1)
                                           (@1ArrayWindow (windows U))
                                           a!17)))
                          (let ((a!19 (ite (= (frame_window (@0ContentElementFrame
                                                              a!12))
                                              0)
                                           (@0ArrayWindow (windows U))
                                           a!18)))
                          (let ((a!41 (= (rp_hd_csp (dc_headers (wd_document a!19)))
                                         (rp_hd_csp (dc_headers a!40))))
                                (a!42 (not ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location a!19)))))
                                (a!43 (not ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location a!19))))))
                          (let ((a!67 (and (Reachable U F1 G1)
                                           (= F1 a!1)
                                           (not a!41)
                                           ((_ is SomeInt)
                                             (ite (= Y 0) a!20 a!29))
                                           a!42
                                           a!43
                                           ((_ is SomeDOMElement)
                                             (ite (= Y 0) a!2 a!11))
                                           (not a!44)
                                           (not ((_ is ContentElementHTML) a!12))
                                           (not ((_ is ContentElementImage)
                                                  a!12))
                                           (not ((_ is ContentElementScript)
                                                  a!12))
                                           (c_csp_inherit_blob_from_creator
                                             (config U))
                                           (c_csp_inherit_local_from_initiator
                                             (config U))
                                           (or a!45 a!62)
                                           (= F1 a!66))))
                            (=> a!67 (query!0 G1 F1 U)))))))))))))))
                          :weight 0))))
      (a!3 (asserted (forall ((A State)
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
                                (a!4 (ite ((_ is EmitterScript) (ft_emitter N1))
                                          (not (= Q1 DOMTopLevel))
                                          (and ((_ is EmitterForm)
                                                 (ft_emitter N1))
                                               (= Q1 DOMTopLevel))))
                                (a!5 (not ((_ is SomeContentType)
                                            (rp_hd_content_type (rp_headers R1)))))
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
                                (a!44 (Build_Initiators NoneInt
                                                        (Build_ArrayoptionInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt
                                                          NoneInt)))
                                (a!47 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document S1)))))
                                (a!48 ((_ is SomeCSP)
                                        (rp_hd_csp (dc_headers (wd_document S1)))))
                                (a!49 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location S1)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location S1)))))
                                (a!50 (SomeOrigin (TupleOrigin (url_protocol (wd_location S1))
                                                               (url_host (wd_location S1))
                                                               (url_port (wd_location S1)))))
                                (a!51 (OpaqueOrigin (@0url_path_data (url_path (wd_location S1)))))
                                (a!53 (SomeOrigin (@0url_path_blob (url_path (wd_location S1)))))
                                (a!86 (script_nonce (@0ContentElementScript
                                                      (@0SomeContentElement
                                                        (rp_content R1)))))
                                (a!87 (@0ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!88 (@1ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!89 (@2ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!90 (@3ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!91 (@4ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!92 (@5ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!93 (@6ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                (a!94 (@defaultArrayoptionInt
                                        (in_body (dc_init (wd_document S1)))))
                                (a!104 (= (rp_hd_csp (rp_headers R1))
                                          (rp_hd_csp (dc_headers (wd_document O1)))))
                                (a!106 (= (@1url_path_blob (url_path (rp_url R1)))
                                          0))
                                (a!107 (= (@1url_path_blob (url_path (rp_url R1)))
                                          1))
                                (a!108 (= (@1url_path_blob (url_path (rp_url R1)))
                                          2))
                                (a!109 (= (@1url_path_blob (url_path (rp_url R1)))
                                          3))
                                (a!110 (= (@1url_path_blob (url_path (rp_url R1)))
                                          4))
                                (a!111 (= (@1url_path_blob (url_path (rp_url R1)))
                                          5))
                                (a!112 (= (@1url_path_blob (url_path (rp_url R1)))
                                          6))
                                (a!121 (frame_window (@0ContentElementFrame
                                                       (@0SomeContentElement
                                                         (rp_content R1)))))
                                (a!125 (html_body (@1ContentElementFrame
                                                    (@0SomeContentElement
                                                      (rp_content R1)))))
                                (a!155 (@0ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!156 (@1ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!157 (@2ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!158 (@3ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!159 (@4ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!160 (@5ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!161 (@6ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!162 (@defaultArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document S1)))))
                                (a!169 (not ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))))
                                (a!170 (SomeDOMElement (DOMElementResource
                                                         (rp_url R1)
                                                         (@0SomeContentElement
                                                           (rp_content R1)))))
                                (a!171 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!172 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!173 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!174 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!175 (@5ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!176 (@6ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!177 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!178 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document S1)))))
                                (a!186 (ite (= M1 5)
                                            (@5ArrayWindow (windows L1))
                                            (ite (= M1 6)
                                                 (@6ArrayWindow (windows L1))
                                                 (@defaultArrayWindow
                                                   (windows L1)))))
                                (a!190 (not (= (rp_hd_content_type
                                                 (rp_headers R1))
                                               NoneContentType)))
                                (a!192 (not ((_ is SomeURL)
                                              (rp_hd_location (rp_headers V)))))
                                (a!194 (ite ((_ is EmitterScript)
                                              (ft_emitter R))
                                            (not (= U DOMTopLevel))
                                            (and ((_ is EmitterForm)
                                                   (ft_emitter R))
                                                 (= U DOMTopLevel))))
                                (a!195 (not ((_ is SomeContentType)
                                              (rp_hd_content_type
                                                (rp_headers V)))))
                                (a!196 (image_src (@0ContentElementImage
                                                    (@0SomeContentElement
                                                      (rp_content V)))))
                                (a!197 (script_src (@0ContentElementScript
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                (a!198 (frame_src (@0ContentElementFrame
                                                    (@0SomeContentElement
                                                      (rp_content V)))))
                                (a!202 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            ContentTypeScript
                                            ContentTypeHTML))
                                (a!207 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!208 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!209 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!210 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!211 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!212 (@5ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!213 (@6ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!214 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document G1)))))
                                (a!218 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url V)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url V)))
                                           (= (rp_hd_csp (rp_headers V))
                                              NoneCSP)))
                                (a!219 (html_body (@0ContentElementHTML
                                                    (@0SomeContentElement
                                                      (rp_content V)))))
                                (a!247 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document W)))))
                                (a!248 ((_ is SomeCSP)
                                         (rp_hd_csp (dc_headers (wd_document W)))))
                                (a!249 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location W)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location W)))))
                                (a!250 (SomeOrigin (TupleOrigin (url_protocol (wd_location W))
                                                                (url_host (wd_location W))
                                                                (url_port (wd_location W)))))
                                (a!251 (OpaqueOrigin (@0url_path_data (url_path (wd_location W)))))
                                (a!253 (SomeOrigin (@0url_path_blob (url_path (wd_location W)))))
                                (a!286 (script_nonce (@0ContentElementScript
                                                       (@0SomeContentElement
                                                         (rp_content V)))))
                                (a!287 (@0ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!288 (@1ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!289 (@2ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!290 (@3ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!291 (@4ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!292 (@5ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!293 (@6ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                (a!294 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document W)))))
                                (a!304 (= (rp_hd_csp (rp_headers V))
                                          (rp_hd_csp (dc_headers (wd_document S)))))
                                (a!306 (= (@1url_path_blob (url_path (rp_url V)))
                                          0))
                                (a!307 (= (@1url_path_blob (url_path (rp_url V)))
                                          1))
                                (a!308 (= (@1url_path_blob (url_path (rp_url V)))
                                          2))
                                (a!309 (= (@1url_path_blob (url_path (rp_url V)))
                                          3))
                                (a!310 (= (@1url_path_blob (url_path (rp_url V)))
                                          4))
                                (a!311 (= (@1url_path_blob (url_path (rp_url V)))
                                          5))
                                (a!312 (= (@1url_path_blob (url_path (rp_url V)))
                                          6))
                                (a!321 (frame_window (@0ContentElementFrame
                                                       (@0SomeContentElement
                                                         (rp_content V)))))
                                (a!325 (html_body (@1ContentElementFrame
                                                    (@0SomeContentElement
                                                      (rp_content V)))))
                                (a!355 (@0ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!356 (@1ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!357 (@2ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!358 (@3ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!359 (@4ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!360 (@5ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!361 (@6ArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!362 (@defaultArrayoptionHTMLElement
                                         (html_body (dc_html (wd_document W)))))
                                (a!369 (not ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))))
                                (a!370 (SomeDOMElement (DOMElementResource
                                                         (rp_url V)
                                                         (@0SomeContentElement
                                                           (rp_content V)))))
                                (a!371 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!372 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!373 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!374 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!375 (@5ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!376 (@6ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!377 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!378 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document W)))))
                                (a!387 (DOMElementResource
                                         (rp_url C1)
                                         (ContentElementFrame
                                           (Build_Frame (frame_src D1) E1)
                                           F1)))
                                (a!394 (ite (= E1 5)
                                            (@5ArrayWindow (windows X))
                                            (ite (= E1 6)
                                                 (@6ArrayWindow (windows X))
                                                 (@defaultArrayWindow
                                                   (windows X)))))
                                (a!398 (ite (= Q 5)
                                            (@5ArrayWindow (windows P))
                                            (ite (= Q 6)
                                                 (@6ArrayWindow (windows P))
                                                 (@defaultArrayWindow
                                                   (windows P)))))
                                (a!402 (ite (= (frame_window D1) 5)
                                            (@5ArrayWindow (windows X))
                                            (ite (= (frame_window D1) 6)
                                                 (@6ArrayWindow (windows X))
                                                 (@defaultArrayWindow
                                                   (windows X)))))
                                (a!406 (not (= (rp_hd_content_type
                                                 (rp_headers V))
                                               NoneContentType)))
                                (a!408 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url I1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url I1)))))
                                (a!409 (SomeOrigin (TupleOrigin (url_protocol (rp_url I1))
                                                                (url_host (rp_url I1))
                                                                (url_port (rp_url I1)))))
                                (a!410 (OpaqueOrigin (@0url_path_data (url_path (rp_url I1)))))
                                (a!412 (SomeOrigin (@0url_path_blob (url_path (rp_url I1)))))
                                (a!416 (ite (= D 5)
                                            (@5ArrayprodOriginoptionCSP
                                              (origin_csp X1))
                                            (ite (= D 6)
                                                 (@6ArrayprodOriginoptionCSP
                                                   (origin_csp X1))
                                                 (@defaultArrayprodOriginoptionCSP
                                                   (origin_csp X1)))))
                                (a!422 (or (and (= U1 DOMTopLevel)
                                                (= F2
                                                   (Build_ArrayoptionBlob
                                                     NoneBlob
                                                     NoneBlob
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
                                              (@5ArrayoptionHTMLElement a!18)))
                                          ((_ is HTMLImage)
                                            (@0SomeHTMLElement
                                              (@5ArrayoptionHTMLElement a!18)))))
                                (a!35 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                (@5ArrayoptionHTMLElement
                                                                  a!18)))
                                                  (@1HTMLForm (@0SomeHTMLElement
                                                                (@5ArrayoptionHTMLElement
                                                                  a!18)))))
                                (a!37 (or ((_ is HTMLScript)
                                            (@0SomeHTMLElement
                                              (@6ArrayoptionHTMLElement a!18)))
                                          ((_ is HTMLImage)
                                            (@0SomeHTMLElement
                                              (@6ArrayoptionHTMLElement a!18)))))
                                (a!38 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                (@6ArrayoptionHTMLElement
                                                                  a!18)))
                                                  (@1HTMLForm (@0SomeHTMLElement
                                                                (@6ArrayoptionHTMLElement
                                                                  a!18)))))
                                (a!40 (or ((_ is HTMLScript)
                                            (@0SomeHTMLElement
                                              (@defaultArrayoptionHTMLElement
                                                a!18)))
                                          ((_ is HTMLImage)
                                            (@0SomeHTMLElement
                                              (@defaultArrayoptionHTMLElement
                                                a!18)))))
                                (a!41 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                (@defaultArrayoptionHTMLElement
                                                                  a!18)))
                                                  (@1HTMLForm (@0SomeHTMLElement
                                                                (@defaultArrayoptionHTMLElement
                                                                  a!18)))))
                                (a!52 (ite ((_ is url_path_data)
                                             (url_path (wd_location S1)))
                                           (SomeOrigin a!51)
                                           NoneOrigin))
                                (a!54 (ite ((_ is url_path_blob)
                                             (url_path (wd_location S1)))
                                           a!53
                                           NoneOrigin))
                                (a!57 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!7)))))
                                (a!58 (ite ((_ is url_path_blob) (url_path a!7))
                                           (SomeOrigin (@0url_path_blob (url_path a!7)))
                                           NoneOrigin))
                                (a!62 (= (url_protocol a!7)
                                         (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!63 ((_ is SomePath)
                                        (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!64 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!66 ((_ is SomeInt)
                                        (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!67 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!68 (= (@0domain (@0SomeDomain (url_host a!7)))
                                         (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!69 (= (@1subdomain (@0SomeDomain (url_host a!7)))
                                         (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!71 ((_ is SomeProtocol)
                                        (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!72 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!75 ((_ is SomeoptionInt)
                                        (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!76 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!78 (not ((_ is domain)
                                             (@0SomeDomain (url_host a!7)))))
                                (a!80 (and ((_ is SomeDomain) (url_host a!7))
                                           ((_ is domain)
                                             (@0SomeDomain (url_host a!7)))))
                                (a!84 (not ((_ is CSPSrcNone)
                                             (@0SomeCSPSrc (csp_script_src a!47)))))
                                (a!95 (ite (= (@0DOMIndex Q1) 5)
                                           a!92
                                           (ite (= (@0DOMIndex Q1) 6) a!93 a!94)))
                                (a!113 (ite a!110
                                            (@4ArrayoptionBlob K1)
                                            (ite a!111
                                                 (@5ArrayoptionBlob K1)
                                                 (ite a!112
                                                      (@6ArrayoptionBlob K1)
                                                      (@defaultArrayoptionBlob
                                                        K1)))))
                                (a!122 (ite (= a!121 5)
                                            (@5ArrayWindow (windows L1))
                                            (ite (= a!121 6)
                                                 (@6ArrayWindow (windows L1))
                                                 (@defaultArrayWindow
                                                   (windows L1)))))
                                (a!126 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!125)))))
                                (a!127 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!129 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!125)))))
                                (a!130 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!132 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!125)))))
                                (a!133 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!135 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!125)))))
                                (a!136 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!138 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!125)))))
                                (a!139 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!141 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!125)))))
                                (a!142 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!144 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!125)))))
                                (a!145 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!147 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!125)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!125)))))
                                (a!148 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!125)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!125)))))
                                (a!163 (ite (= (@0DOMIndex Q1) 5)
                                            a!160
                                            (ite (= (@0DOMIndex Q1) 6)
                                                 a!161
                                                 a!162)))
                                (a!179 (ite (= (@0DOMIndex Q1) 6)
                                            (Build_ArrayoptionDOMElement
                                              a!178
                                              a!171
                                              a!172
                                              a!173
                                              a!174
                                              a!175
                                              a!170
                                              a!177)
                                            (dm_body (dc_dom (wd_document S1)))))
                                (a!187 (ite (= M1 3)
                                            (@3ArrayWindow (windows L1))
                                            (ite (= M1 4)
                                                 (@4ArrayWindow (windows L1))
                                                 a!186)))
                                (a!193 (and a!192
                                            (not ((_ is ResponseNoContent)
                                                   (rp_code V)))))
                                (a!199 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (= a!197 (rp_url V))
                                            (= a!198 (rp_url V))))
                                (a!203 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            ContentTypeImage
                                            a!202))
                                (a!215 (ite (= B1 4)
                                            a!211
                                            (ite (= B1 5)
                                                 a!212
                                                 (ite (= B1 6) a!213 a!214))))
                                (a!220 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!219)))))
                                (a!221 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!223 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!219)))))
                                (a!224 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!226 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!219)))))
                                (a!227 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!229 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!219)))))
                                (a!230 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!232 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!219)))))
                                (a!233 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!235 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!219)))))
                                (a!236 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!238 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!219)))))
                                (a!239 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!241 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!219)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!219)))))
                                (a!242 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!219)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!219)))))
                                (a!252 (ite ((_ is url_path_data)
                                              (url_path (wd_location W)))
                                            (SomeOrigin a!251)
                                            NoneOrigin))
                                (a!254 (ite ((_ is url_path_blob)
                                              (url_path (wd_location W)))
                                            a!253
                                            NoneOrigin))
                                (a!257 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!197)))))
                                (a!258 (ite ((_ is url_path_blob)
                                              (url_path a!197))
                                            (SomeOrigin (@0url_path_blob (url_path a!197)))
                                            NoneOrigin))
                                (a!262 (= (url_protocol a!197)
                                          (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!263 ((_ is SomePath)
                                         (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!264 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!266 ((_ is SomeInt)
                                         (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!267 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!268 (= (@0domain (@0SomeDomain (url_host a!197)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!269 (= (@1subdomain (@0SomeDomain (url_host a!197)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!271 ((_ is SomeProtocol)
                                         (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!272 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!275 ((_ is SomeoptionInt)
                                         (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!276 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!278 (not ((_ is domain)
                                              (@0SomeDomain (url_host a!197)))))
                                (a!280 (and ((_ is SomeDomain) (url_host a!197))
                                            ((_ is domain)
                                              (@0SomeDomain (url_host a!197)))))
                                (a!284 (not ((_ is CSPSrcNone)
                                              (@0SomeCSPSrc (csp_script_src a!247)))))
                                (a!295 (ite (= (@0DOMIndex U) 5)
                                            a!292
                                            (ite (= (@0DOMIndex U) 6)
                                                 a!293
                                                 a!294)))
                                (a!313 (ite a!310
                                            (@4ArrayoptionBlob O)
                                            (ite a!311
                                                 (@5ArrayoptionBlob O)
                                                 (ite a!312
                                                      (@6ArrayoptionBlob O)
                                                      (@defaultArrayoptionBlob
                                                        O)))))
                                (a!322 (ite (= a!321 5)
                                            (@5ArrayWindow (windows P))
                                            (ite (= a!321 6)
                                                 (@6ArrayWindow (windows P))
                                                 (@defaultArrayWindow
                                                   (windows P)))))
                                (a!326 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!325)))))
                                (a!327 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!329 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@1ArrayoptionHTMLElement a!325)))))
                                (a!330 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@1ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!332 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@2ArrayoptionHTMLElement a!325)))))
                                (a!333 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@2ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!335 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@3ArrayoptionHTMLElement a!325)))))
                                (a!336 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@3ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!338 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@4ArrayoptionHTMLElement a!325)))))
                                (a!339 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@4ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!341 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@5ArrayoptionHTMLElement a!325)))))
                                (a!342 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@5ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!344 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!325)))))
                                (a!345 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@6ArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!347 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!325)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!325)))))
                                (a!348 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!325)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@defaultArrayoptionHTMLElement
                                                                   a!325)))))
                                (a!363 (ite (= (@0DOMIndex U) 5)
                                            a!360
                                            (ite (= (@0DOMIndex U) 6)
                                                 a!361
                                                 a!362)))
                                (a!379 (ite (= (@0DOMIndex U) 6)
                                            (Build_ArrayoptionDOMElement
                                              a!378
                                              a!371
                                              a!372
                                              a!373
                                              a!374
                                              a!375
                                              a!370
                                              a!377)
                                            (dm_body (dc_dom (wd_document W)))))
                                (a!388 (ite (= B1 6)
                                            (Build_ArrayoptionDOMElement
                                              a!207
                                              a!208
                                              a!209
                                              a!210
                                              a!211
                                              a!212
                                              (SomeDOMElement a!387)
                                              a!214)
                                            (dm_body (dc_dom (wd_document G1)))))
                                (a!395 (ite (= E1 3)
                                            (@3ArrayWindow (windows X))
                                            (ite (= E1 4)
                                                 (@4ArrayWindow (windows X))
                                                 a!394)))
                                (a!399 (ite (= Q 3)
                                            (@3ArrayWindow (windows P))
                                            (ite (= Q 4)
                                                 (@4ArrayWindow (windows P))
                                                 a!398)))
                                (a!403 (ite (= (frame_window D1) 3)
                                            (@3ArrayWindow (windows X))
                                            (ite (= (frame_window D1) 4)
                                                 (@4ArrayWindow (windows X))
                                                 a!402)))
                                (a!411 (ite ((_ is url_path_data)
                                              (url_path (rp_url I1)))
                                            (SomeOrigin a!410)
                                            NoneOrigin))
                                (a!413 (ite ((_ is url_path_blob)
                                              (url_path (rp_url I1)))
                                            a!412
                                            NoneOrigin))
                                (a!417 (ite (= D 3)
                                            (@3ArrayprodOriginoptionCSP
                                              (origin_csp X1))
                                            (ite (= D 4)
                                                 (@4ArrayprodOriginoptionCSP
                                                   (origin_csp X1))
                                                 a!416))))
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
                                               (@5ArrayoptionHTMLElement a!18)))
                                           (SomeDOMElement (DOMElementForm a!35))
                                           NoneDOMElement))
                                (a!39 (ite ((_ is HTMLForm)
                                             (@0SomeHTMLElement
                                               (@6ArrayoptionHTMLElement a!18)))
                                           (SomeDOMElement (DOMElementForm a!38))
                                           NoneDOMElement))
                                (a!42 (ite ((_ is HTMLForm)
                                             (@0SomeHTMLElement
                                               (@defaultArrayoptionHTMLElement
                                                 a!18)))
                                           (SomeDOMElement (DOMElementForm a!41))
                                           NoneDOMElement))
                                (a!55 (ite ((_ is url_path_data)
                                             (url_path (wd_location S1)))
                                           NoneOrigin
                                           a!54))
                                (a!59 (ite ((_ is ProtocolData)
                                             (url_protocol a!7))
                                           (ite ((_ is url_path_data)
                                                  (url_path a!7))
                                                a!57
                                                NoneOrigin)
                                           (ite ((_ is url_path_data)
                                                  (url_path a!7))
                                                NoneOrigin
                                                a!58)))
                                (a!65 (and (not ((_ is url_path_blob)
                                                  (url_path a!7)))
                                           (not ((_ is url_path_data)
                                                  (url_path a!7)))
                                           (= (@0url_path_res (url_path a!7))
                                              a!64)))
                                (a!70 (ite ((_ is domain)
                                             (@0SomeDomain (url_host a!7)))
                                           a!68
                                           a!69))
                                (a!77 (= (@0subdomain (@0SomeDomain (url_host a!7)))
                                         (@0SomeInt a!76)))
                                (a!96 (ite (= (@0DOMIndex Q1) 3)
                                           a!90
                                           (ite (= (@0DOMIndex Q1) 4) a!91 a!95)))
                                (a!114 (ite a!107
                                            (@1ArrayoptionBlob K1)
                                            (ite a!108
                                                 (@2ArrayoptionBlob K1)
                                                 (ite a!109
                                                      (@3ArrayoptionBlob K1)
                                                      a!113))))
                                (a!123 (ite (= a!121 3)
                                            (@3ArrayWindow (windows L1))
                                            (ite (= a!121 4)
                                                 (@4ArrayWindow (windows L1))
                                                 a!122)))
                                (a!128 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!127))
                                            NoneDOMElement))
                                (a!131 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!130))
                                            NoneDOMElement))
                                (a!134 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!133))
                                            NoneDOMElement))
                                (a!137 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!136))
                                            NoneDOMElement))
                                (a!140 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!139))
                                            NoneDOMElement))
                                (a!143 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@5ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!142))
                                            NoneDOMElement))
                                (a!146 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@6ArrayoptionHTMLElement a!125)))
                                            (SomeDOMElement (DOMElementForm a!145))
                                            NoneDOMElement))
                                (a!149 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!125)))
                                            (SomeDOMElement (DOMElementForm a!148))
                                            NoneDOMElement))
                                (a!164 (ite (= (@0DOMIndex Q1) 3)
                                            a!158
                                            (ite (= (@0DOMIndex Q1) 4)
                                                 a!159
                                                 a!163)))
                                (a!180 (ite (= (@0DOMIndex Q1) 4)
                                            (Build_ArrayoptionDOMElement
                                              a!178
                                              a!171
                                              a!172
                                              a!173
                                              a!170
                                              a!175
                                              a!176
                                              a!177)
                                            (ite (= (@0DOMIndex Q1) 5)
                                                 (Build_ArrayoptionDOMElement
                                                   a!178
                                                   a!171
                                                   a!172
                                                   a!173
                                                   a!174
                                                   a!170
                                                   a!176
                                                   a!177)
                                                 a!179)))
                                (a!188 (ite (= M1 1)
                                            (@1ArrayWindow (windows L1))
                                            (ite (= M1 2)
                                                 (@2ArrayWindow (windows L1))
                                                 a!187)))
                                (a!200 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (= a!196 (rp_url V))
                                            a!199))
                                (a!204 (ite ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            ContentTypeHTML
                                            a!203))
                                (a!216 (ite (= B1 1)
                                            a!208
                                            (ite (= B1 2)
                                                 a!209
                                                 (ite (= B1 3) a!210 a!215))))
                                (a!222 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!221))
                                            NoneDOMElement))
                                (a!225 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!224))
                                            NoneDOMElement))
                                (a!228 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!227))
                                            NoneDOMElement))
                                (a!231 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!230))
                                            NoneDOMElement))
                                (a!234 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!233))
                                            NoneDOMElement))
                                (a!237 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@5ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!236))
                                            NoneDOMElement))
                                (a!240 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@6ArrayoptionHTMLElement a!219)))
                                            (SomeDOMElement (DOMElementForm a!239))
                                            NoneDOMElement))
                                (a!243 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!219)))
                                            (SomeDOMElement (DOMElementForm a!242))
                                            NoneDOMElement))
                                (a!255 (ite ((_ is url_path_data)
                                              (url_path (wd_location W)))
                                            NoneOrigin
                                            a!254))
                                (a!259 (ite ((_ is ProtocolData)
                                              (url_protocol a!197))
                                            (ite ((_ is url_path_data)
                                                   (url_path a!197))
                                                 a!257
                                                 NoneOrigin)
                                            (ite ((_ is url_path_data)
                                                   (url_path a!197))
                                                 NoneOrigin
                                                 a!258)))
                                (a!265 (and (not ((_ is url_path_blob)
                                                   (url_path a!197)))
                                            (not ((_ is url_path_data)
                                                   (url_path a!197)))
                                            (= (@0url_path_res (url_path a!197))
                                               a!264)))
                                (a!270 (ite ((_ is domain)
                                              (@0SomeDomain (url_host a!197)))
                                            a!268
                                            a!269))
                                (a!277 (= (@0subdomain (@0SomeDomain (url_host a!197)))
                                          (@0SomeInt a!276)))
                                (a!296 (ite (= (@0DOMIndex U) 3)
                                            a!290
                                            (ite (= (@0DOMIndex U) 4)
                                                 a!291
                                                 a!295)))
                                (a!314 (ite a!307
                                            (@1ArrayoptionBlob O)
                                            (ite a!308
                                                 (@2ArrayoptionBlob O)
                                                 (ite a!309
                                                      (@3ArrayoptionBlob O)
                                                      a!313))))
                                (a!323 (ite (= a!321 3)
                                            (@3ArrayWindow (windows P))
                                            (ite (= a!321 4)
                                                 (@4ArrayWindow (windows P))
                                                 a!322)))
                                (a!328 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!327))
                                            NoneDOMElement))
                                (a!331 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!330))
                                            NoneDOMElement))
                                (a!334 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!333))
                                            NoneDOMElement))
                                (a!337 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!336))
                                            NoneDOMElement))
                                (a!340 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!339))
                                            NoneDOMElement))
                                (a!343 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@5ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!342))
                                            NoneDOMElement))
                                (a!346 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@6ArrayoptionHTMLElement a!325)))
                                            (SomeDOMElement (DOMElementForm a!345))
                                            NoneDOMElement))
                                (a!349 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!325)))
                                            (SomeDOMElement (DOMElementForm a!348))
                                            NoneDOMElement))
                                (a!364 (ite (= (@0DOMIndex U) 3)
                                            a!358
                                            (ite (= (@0DOMIndex U) 4)
                                                 a!359
                                                 a!363)))
                                (a!380 (ite (= (@0DOMIndex U) 4)
                                            (Build_ArrayoptionDOMElement
                                              a!378
                                              a!371
                                              a!372
                                              a!373
                                              a!370
                                              a!375
                                              a!376
                                              a!377)
                                            (ite (= (@0DOMIndex U) 5)
                                                 (Build_ArrayoptionDOMElement
                                                   a!378
                                                   a!371
                                                   a!372
                                                   a!373
                                                   a!374
                                                   a!370
                                                   a!376
                                                   a!377)
                                                 a!379)))
                                (a!389 (ite (= B1 4)
                                            (Build_ArrayoptionDOMElement
                                              a!207
                                              a!208
                                              a!209
                                              a!210
                                              (SomeDOMElement a!387)
                                              a!212
                                              a!213
                                              a!214)
                                            (ite (= B1 5)
                                                 (Build_ArrayoptionDOMElement
                                                   a!207
                                                   a!208
                                                   a!209
                                                   a!210
                                                   a!211
                                                   (SomeDOMElement a!387)
                                                   a!213
                                                   a!214)
                                                 a!388)))
                                (a!396 (ite (= E1 1)
                                            (@1ArrayWindow (windows X))
                                            (ite (= E1 2)
                                                 (@2ArrayWindow (windows X))
                                                 a!395)))
                                (a!400 (ite (= Q 1)
                                            (@1ArrayWindow (windows P))
                                            (ite (= Q 2)
                                                 (@2ArrayWindow (windows P))
                                                 a!399)))
                                (a!404 (ite (= (frame_window D1) 1)
                                            (@1ArrayWindow (windows X))
                                            (ite (= (frame_window D1) 2)
                                                 (@2ArrayWindow (windows X))
                                                 a!403)))
                                (a!414 (ite ((_ is url_path_data)
                                              (url_path (rp_url I1)))
                                            NoneOrigin
                                            a!413))
                                (a!418 (ite (= D 1)
                                            (@1ArrayprodOriginoptionCSP
                                              (origin_csp X1))
                                            (ite (= D 2)
                                                 (@2ArrayprodOriginoptionCSP
                                                   (origin_csp X1))
                                                 a!417))))
                          (let ((a!11 (or ((_ is ContentElementHTML)
                                            (@0SomeContentElement
                                              (rp_content R1)))
                                          a!10))
                                (a!15 (= a!14
                                         (@0SomeContentType
                                           (rp_hd_content_type (rp_headers R1)))))
                                (a!43 (Build_ArrayoptionDOMElement
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
                                               (@5ArrayoptionHTMLElement a!18))
                                             (ite a!34 NoneDOMElement a!36)
                                             NoneDOMElement)
                                        (ite ((_ is SomeHTMLElement)
                                               (@6ArrayoptionHTMLElement a!18))
                                             (ite a!37 NoneDOMElement a!39)
                                             NoneDOMElement)
                                        (ite ((_ is SomeHTMLElement)
                                               (@defaultArrayoptionHTMLElement
                                                 a!18))
                                             (ite a!40 NoneDOMElement a!42)
                                             NoneDOMElement)))
                                (a!56 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location S1)))
                                           a!52
                                           a!55))
                                (a!60 (ite (or ((_ is ProtocolHTTPS)
                                                 (url_protocol a!7))
                                               ((_ is ProtocolHTTP)
                                                 (url_protocol a!7)))
                                           (SomeOrigin (TupleOrigin (url_protocol a!7)
                                                                    (url_host a!7)
                                                                    (url_port a!7)))
                                           a!59))
                                (a!79 (ite ((_ is SomeInt) a!76)
                                           (and a!77
                                                ((_ is SomeDomain)
                                                  (url_host a!7))
                                                a!78)
                                           (and ((_ is SomeDomain)
                                                  (url_host a!7))
                                                a!78)))
                                (a!97 (ite (= (@0DOMIndex Q1) 1)
                                           a!88
                                           (ite (= (@0DOMIndex Q1) 2) a!89 a!96)))
                                (a!115 (blob_csp (@0SomeBlob (ite a!106
                                                                  (@0ArrayoptionBlob
                                                                    K1)
                                                                  a!114))))
                                (a!124 (ite (= a!121 1)
                                            (@1ArrayWindow (windows L1))
                                            (ite (= a!121 2)
                                                 (@2ArrayWindow (windows L1))
                                                 a!123)))
                                (a!150 (Build_ArrayoptionDOMElement
                                         (ite ((_ is SomeHTMLElement)
                                                (@0ArrayoptionHTMLElement a!125))
                                              (ite a!126 NoneDOMElement a!128)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@1ArrayoptionHTMLElement a!125))
                                              (ite a!129 NoneDOMElement a!131)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@2ArrayoptionHTMLElement a!125))
                                              (ite a!132 NoneDOMElement a!134)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@3ArrayoptionHTMLElement a!125))
                                              (ite a!135 NoneDOMElement a!137)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@4ArrayoptionHTMLElement a!125))
                                              (ite a!138 NoneDOMElement a!140)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@5ArrayoptionHTMLElement a!125))
                                              (ite a!141 NoneDOMElement a!143)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@6ArrayoptionHTMLElement a!125))
                                              (ite a!144 NoneDOMElement a!146)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@defaultArrayoptionHTMLElement
                                                  a!125))
                                              (ite a!147 NoneDOMElement a!149)
                                              NoneDOMElement)))
                                (a!165 (ite (= (@0DOMIndex Q1) 1)
                                            a!156
                                            (ite (= (@0DOMIndex Q1) 2)
                                                 a!157
                                                 a!164)))
                                (a!181 (ite (= (@0DOMIndex Q1) 2)
                                            (Build_ArrayoptionDOMElement
                                              a!178
                                              a!171
                                              a!170
                                              a!173
                                              a!174
                                              a!175
                                              a!176
                                              a!177)
                                            (ite (= (@0DOMIndex Q1) 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!178
                                                   a!171
                                                   a!172
                                                   a!170
                                                   a!174
                                                   a!175
                                                   a!176
                                                   a!177)
                                                 a!180)))
                                (a!189 (= (ite (= M1 0)
                                               (@0ArrayWindow (windows L1))
                                               a!188)
                                          O1))
                                (a!201 (or ((_ is ContentElementHTML)
                                             (@0SomeContentElement
                                               (rp_content V)))
                                           a!200))
                                (a!205 (= a!204
                                          (@0SomeContentType
                                            (rp_hd_content_type (rp_headers V)))))
                                (a!217 (@1DOMElementResource
                                         (@0SomeDOMElement (ite (= B1 0)
                                                                a!207
                                                                a!216))))
                                (a!244 (Build_ArrayoptionDOMElement
                                         (ite ((_ is SomeHTMLElement)
                                                (@0ArrayoptionHTMLElement a!219))
                                              (ite a!220 NoneDOMElement a!222)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@1ArrayoptionHTMLElement a!219))
                                              (ite a!223 NoneDOMElement a!225)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@2ArrayoptionHTMLElement a!219))
                                              (ite a!226 NoneDOMElement a!228)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@3ArrayoptionHTMLElement a!219))
                                              (ite a!229 NoneDOMElement a!231)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@4ArrayoptionHTMLElement a!219))
                                              (ite a!232 NoneDOMElement a!234)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@5ArrayoptionHTMLElement a!219))
                                              (ite a!235 NoneDOMElement a!237)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@6ArrayoptionHTMLElement a!219))
                                              (ite a!238 NoneDOMElement a!240)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@defaultArrayoptionHTMLElement
                                                  a!219))
                                              (ite a!241 NoneDOMElement a!243)
                                              NoneDOMElement)))
                                (a!256 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location W)))
                                            a!252
                                            a!255))
                                (a!260 (ite (or ((_ is ProtocolHTTPS)
                                                  (url_protocol a!197))
                                                ((_ is ProtocolHTTP)
                                                  (url_protocol a!197)))
                                            (SomeOrigin (TupleOrigin (url_protocol a!197)
                                                                     (url_host a!197)
                                                                     (url_port a!197)))
                                            a!259))
                                (a!279 (ite ((_ is SomeInt) a!276)
                                            (and a!277
                                                 ((_ is SomeDomain)
                                                   (url_host a!197))
                                                 a!278)
                                            (and ((_ is SomeDomain)
                                                   (url_host a!197))
                                                 a!278)))
                                (a!297 (ite (= (@0DOMIndex U) 1)
                                            a!288
                                            (ite (= (@0DOMIndex U) 2)
                                                 a!289
                                                 a!296)))
                                (a!315 (blob_csp (@0SomeBlob (ite a!306
                                                                  (@0ArrayoptionBlob
                                                                    O)
                                                                  a!314))))
                                (a!324 (ite (= a!321 1)
                                            (@1ArrayWindow (windows P))
                                            (ite (= a!321 2)
                                                 (@2ArrayWindow (windows P))
                                                 a!323)))
                                (a!350 (Build_ArrayoptionDOMElement
                                         (ite ((_ is SomeHTMLElement)
                                                (@0ArrayoptionHTMLElement a!325))
                                              (ite a!326 NoneDOMElement a!328)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@1ArrayoptionHTMLElement a!325))
                                              (ite a!329 NoneDOMElement a!331)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@2ArrayoptionHTMLElement a!325))
                                              (ite a!332 NoneDOMElement a!334)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@3ArrayoptionHTMLElement a!325))
                                              (ite a!335 NoneDOMElement a!337)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@4ArrayoptionHTMLElement a!325))
                                              (ite a!338 NoneDOMElement a!340)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@5ArrayoptionHTMLElement a!325))
                                              (ite a!341 NoneDOMElement a!343)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@6ArrayoptionHTMLElement a!325))
                                              (ite a!344 NoneDOMElement a!346)
                                              NoneDOMElement)
                                         (ite ((_ is SomeHTMLElement)
                                                (@defaultArrayoptionHTMLElement
                                                  a!325))
                                              (ite a!347 NoneDOMElement a!349)
                                              NoneDOMElement)))
                                (a!365 (ite (= (@0DOMIndex U) 1)
                                            a!356
                                            (ite (= (@0DOMIndex U) 2)
                                                 a!357
                                                 a!364)))
                                (a!381 (ite (= (@0DOMIndex U) 2)
                                            (Build_ArrayoptionDOMElement
                                              a!378
                                              a!371
                                              a!370
                                              a!373
                                              a!374
                                              a!375
                                              a!376
                                              a!377)
                                            (ite (= (@0DOMIndex U) 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!378
                                                   a!371
                                                   a!372
                                                   a!370
                                                   a!374
                                                   a!375
                                                   a!376
                                                   a!377)
                                                 a!380)))
                                (a!386 ((_ is DOMElementForm)
                                         (@0SomeDOMElement (ite (= B1 0)
                                                                a!207
                                                                a!216))))
                                (a!390 (ite (= B1 2)
                                            (Build_ArrayoptionDOMElement
                                              a!207
                                              a!208
                                              (SomeDOMElement a!387)
                                              a!210
                                              a!211
                                              a!212
                                              a!213
                                              a!214)
                                            (ite (= B1 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!207
                                                   a!208
                                                   a!209
                                                   (SomeDOMElement a!387)
                                                   a!211
                                                   a!212
                                                   a!213
                                                   a!214)
                                                 a!389)))
                                (a!397 (= (ite (= E1 0)
                                               (@0ArrayWindow (windows X))
                                               a!396)
                                          Y))
                                (a!401 (= (ite (= Q 0)
                                               (@0ArrayWindow (windows P))
                                               a!400)
                                          S))
                                (a!405 (= (ite (= (frame_window D1) 0)
                                               (@0ArrayWindow (windows X))
                                               a!404)
                                          I))
                                (a!415 (ite ((_ is ProtocolData)
                                              (url_protocol (rp_url I1)))
                                            a!411
                                            a!414))
                                (a!419 (= (ite (= D 0)
                                               (@0ArrayprodOriginoptionCSP
                                                 (origin_csp X1))
                                               a!418)
                                          (pairOriginoptionCSP E G))))
                          (let ((a!16 (or (not ((_ is SomeContentElement)
                                                 (rp_content R1)))
                                          a!5
                                          (and a!11 a!15)))
                                (a!45 (Build_Document (+ 1 P1)
                                                      (ft_correlator N1)
                                                      (rp_headers R1)
                                                      (@0ContentElementHTML
                                                        (@0SomeContentElement
                                                          (rp_content R1)))
                                                      (Build_DOM (ft_correlator N1)
                                                                 0
                                                                 a!43)
                                                      a!44))
                                (a!61 (= (SomeOrigin (@0SomeOrigin (ite a!49
                                                                        a!50
                                                                        a!56)))
                                         a!60))
                                (a!73 (not ((_ is TupleOrigin)
                                             (@0SomeOrigin (ite a!49 a!50 a!56)))))
                                (a!74 (= (url_protocol a!7)
                                         (@0TupleOrigin (@0SomeOrigin (ite a!49
                                                                           a!50
                                                                           a!56)))))
                                (a!98 ((_ is SomeInt)
                                        (ite (= (@0DOMIndex Q1) 0) a!87 a!97)))
                                (a!99 (@0SomeInt (ite (= (@0DOMIndex Q1) 0)
                                                      a!87
                                                      a!97)))
                                (a!151 (Build_Document (+ 1 P1)
                                                       (ft_correlator N1)
                                                       (rp_headers R1)
                                                       (@1ContentElementFrame
                                                         (@0SomeContentElement
                                                           (rp_content R1)))
                                                       (Build_DOM (ft_correlator N1)
                                                                  0
                                                                  a!150)
                                                       a!44))
                                (a!166 (@0SomeHTMLElement
                                         (ite (= (@0DOMIndex Q1) 0) a!155 a!165)))
                                (a!182 (ite (= (@0DOMIndex Q1) 0)
                                            (Build_ArrayoptionDOMElement
                                              a!170
                                              a!171
                                              a!172
                                              a!173
                                              a!174
                                              a!175
                                              a!176
                                              a!177)
                                            (ite (= (@0DOMIndex Q1) 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!178
                                                   a!170
                                                   a!172
                                                   a!173
                                                   a!174
                                                   a!175
                                                   a!176
                                                   a!177)
                                                 a!181)))
                                (a!185 ((_ is SomeHTMLElement)
                                         (ite (= (@0DOMIndex Q1) 0) a!155 a!165)))
                                (a!206 (or (not ((_ is SomeContentElement)
                                                  (rp_content V)))
                                           a!195
                                           (and a!201 a!205)))
                                (a!245 (Build_Document (+ 1 T)
                                                       (ft_correlator R)
                                                       (rp_headers V)
                                                       (@0ContentElementHTML
                                                         (@0SomeContentElement
                                                           (rp_content V)))
                                                       (Build_DOM (ft_correlator R)
                                                                  0
                                                                  a!244)
                                                       a!44))
                                (a!261 (= (SomeOrigin (@0SomeOrigin (ite a!249
                                                                         a!250
                                                                         a!256)))
                                          a!260))
                                (a!273 (not ((_ is TupleOrigin)
                                              (@0SomeOrigin (ite a!249
                                                                 a!250
                                                                 a!256)))))
                                (a!274 (= (url_protocol a!197)
                                          (@0TupleOrigin (@0SomeOrigin (ite a!249
                                                                            a!250
                                                                            a!256)))))
                                (a!298 ((_ is SomeInt)
                                         (ite (= (@0DOMIndex U) 0) a!287 a!297)))
                                (a!299 (@0SomeInt (ite (= (@0DOMIndex U) 0)
                                                       a!287
                                                       a!297)))
                                (a!351 (Build_Document (+ 1 T)
                                                       (ft_correlator R)
                                                       (rp_headers V)
                                                       (@1ContentElementFrame
                                                         (@0SomeContentElement
                                                           (rp_content V)))
                                                       (Build_DOM (ft_correlator R)
                                                                  0
                                                                  a!350)
                                                       a!44))
                                (a!366 (@0SomeHTMLElement
                                         (ite (= (@0DOMIndex U) 0) a!355 a!365)))
                                (a!382 (ite (= (@0DOMIndex U) 0)
                                            (Build_ArrayoptionDOMElement
                                              a!370
                                              a!371
                                              a!372
                                              a!373
                                              a!374
                                              a!375
                                              a!376
                                              a!377)
                                            (ite (= (@0DOMIndex U) 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!378
                                                   a!370
                                                   a!372
                                                   a!373
                                                   a!374
                                                   a!375
                                                   a!376
                                                   a!377)
                                                 a!381)))
                                (a!385 ((_ is SomeHTMLElement)
                                         (ite (= (@0DOMIndex U) 0) a!355 a!365)))
                                (a!391 (ite (= B1 0)
                                            (Build_ArrayoptionDOMElement
                                              (SomeDOMElement a!387)
                                              a!208
                                              a!209
                                              a!210
                                              a!211
                                              a!212
                                              a!213
                                              a!214)
                                            (ite (= B1 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!207
                                                   (SomeDOMElement a!387)
                                                   a!209
                                                   a!210
                                                   a!211
                                                   a!212
                                                   a!213
                                                   a!214)
                                                 a!390)))
                                (a!420 (and (c_origin_wide_csp (config X1))
                                            (= (ite a!408 a!409 a!415)
                                               (SomeOrigin F))
                                            a!419
                                            (= E F)
                                            (= (rp_hd_csp (rp_headers I1)) G))))
                          (let ((a!46 (and a!17
                                           ((_ is ContentElementHTML)
                                             (@0SomeContentElement
                                               (rp_content R1)))
                                           (= O1
                                              (Build_Window (ft_correlator N1)
                                                            NoneInt
                                                            (rp_url R1)
                                                            NoneDomain
                                                            a!45))))
                                (a!81 (and (or (not a!63) a!65)
                                           (or (not a!66)
                                               (= (url_port a!7) (SomeInt a!67)))
                                           a!70
                                           (ite a!71
                                                (= (url_protocol a!7) a!72)
                                                (or a!73 a!74))
                                           (ite a!75 a!79 a!80)
                                           ((_ is SomeDomain) (url_host a!7))))
                                (a!100 (ite (= a!99 5)
                                            (@5ArrayWindow (windows L1))
                                            (ite (= a!99 6)
                                                 (@6ArrayWindow (windows L1))
                                                 (@defaultArrayWindow
                                                   (windows L1)))))
                                (a!152 (= (ite (= a!121 0)
                                               (@0ArrayWindow (windows L1))
                                               a!124)
                                          (Build_Window (ft_correlator N1)
                                                        (SomeInt M1)
                                                        (rp_url R1)
                                                        NoneDomain
                                                        a!151)))
                                (a!167 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            (= a!166 (HTMLScript a!7))
                                            (= a!166 (HTMLFrame a!8))))
                                (a!183 (Build_DOM (dm_nonce (dc_dom (wd_document S1)))
                                                  (dm_head (dc_dom (wd_document S1)))
                                                  a!182))
                                (a!246 (and a!218
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (= S
                                               (Build_Window (ft_correlator R)
                                                             NoneInt
                                                             (rp_url V)
                                                             NoneDomain
                                                             a!245))))
                                (a!281 (and (or (not a!263) a!265)
                                            (or (not a!266)
                                                (= (url_port a!197)
                                                   (SomeInt a!267)))
                                            a!270
                                            (ite a!271
                                                 (= (url_protocol a!197) a!272)
                                                 (or a!273 a!274))
                                            (ite a!275 a!279 a!280)
                                            ((_ is SomeDomain) (url_host a!197))))
                                (a!300 (ite (= a!299 5)
                                            (@5ArrayWindow (windows P))
                                            (ite (= a!299 6)
                                                 (@6ArrayWindow (windows P))
                                                 (@defaultArrayWindow
                                                   (windows P)))))
                                (a!352 (= (ite (= a!321 0)
                                               (@0ArrayWindow (windows P))
                                               a!324)
                                          (Build_Window (ft_correlator R)
                                                        (SomeInt Q)
                                                        (rp_url V)
                                                        NoneDomain
                                                        a!351)))
                                (a!367 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (= a!366 (HTMLScript a!197))
                                            (= a!366 (HTMLFrame a!198))))
                                (a!383 (Build_DOM (dm_nonce (dc_dom (wd_document W)))
                                                  (dm_head (dc_dom (wd_document W)))
                                                  a!382))
                                (a!392 (Build_DOM (dm_nonce (dc_dom (wd_document G1)))
                                                  (dm_head (dc_dom (wd_document G1)))
                                                  a!391))
                                (a!421 (or (not (c_origin_wide_csp (config X1)))
                                           a!420)))
                          (let ((a!82 (ite ((_ is CSPSrcScheme)
                                             (@0SomeCSPSrc (csp_script_src a!47)))
                                           a!62
                                           a!81))
                                (a!101 (ite (= a!99 3)
                                            (@3ArrayWindow (windows L1))
                                            (ite (= a!99 4)
                                                 (@4ArrayWindow (windows L1))
                                                 a!100)))
                                (a!168 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            (= a!166 (HTMLImage a!6))
                                            a!167))
                                (a!184 (Build_Window (wd_nonce S1)
                                                     (wd_parent S1)
                                                     (wd_location S1)
                                                     (wd_document_domain S1)
                                                     (Build_Document (+ 1 P1)
                                                                     (dc_nonce (wd_document S1))
                                                                     (dc_headers (wd_document S1))
                                                                     (dc_html (wd_document S1))
                                                                     a!183
                                                                     (dc_init (wd_document S1)))))
                                (a!282 (ite ((_ is CSPSrcScheme)
                                              (@0SomeCSPSrc (csp_script_src a!247)))
                                            a!262
                                            a!281))
                                (a!301 (ite (= a!299 3)
                                            (@3ArrayWindow (windows P))
                                            (ite (= a!299 4)
                                                 (@4ArrayWindow (windows P))
                                                 a!300)))
                                (a!368 (ite ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (= a!366 (HTMLImage a!196))
                                            a!367))
                                (a!384 (Build_Window (wd_nonce W)
                                                     (wd_parent W)
                                                     (wd_location W)
                                                     (wd_document_domain W)
                                                     (Build_Document (+ 1 T)
                                                                     (dc_nonce (wd_document W))
                                                                     (dc_headers (wd_document W))
                                                                     (dc_html (wd_document W))
                                                                     a!383
                                                                     (dc_init (wd_document W)))))
                                (a!393 (Build_Window (wd_nonce G1)
                                                     (wd_parent G1)
                                                     (wd_location G1)
                                                     (wd_document_domain G1)
                                                     (Build_Document (+ 1 A1)
                                                                     (dc_nonce (wd_document G1))
                                                                     (dc_headers (wd_document G1))
                                                                     (dc_html (wd_document G1))
                                                                     a!392
                                                                     (dc_init (wd_document G1))))))
                          (let ((a!83 (ite ((_ is CSPSrcSelf)
                                             (@0SomeCSPSrc (csp_script_src a!47)))
                                           a!61
                                           a!82))
                                (a!102 (ite (= a!99 1)
                                            (@1ArrayWindow (windows L1))
                                            (ite (= a!99 2)
                                                 (@2ArrayWindow (windows L1))
                                                 a!101)))
                                (a!283 (ite ((_ is CSPSrcSelf)
                                              (@0SomeCSPSrc (csp_script_src a!247)))
                                            a!261
                                            a!282))
                                (a!302 (ite (= a!299 1)
                                            (@1ArrayWindow (windows P))
                                            (ite (= a!299 2)
                                                 (@2ArrayWindow (windows P))
                                                 a!301))))
                          (let ((a!85 (or (not ((_ is SomeCSPSrc)
                                                 (csp_script_src a!47)))
                                          (not a!48)
                                          (and a!83
                                               ((_ is SomeOrigin)
                                                 (ite a!49 a!50 a!56))
                                               a!84)))
                                (a!103 (wd_document (ite (= a!99 0)
                                                         (@0ArrayWindow (windows L1))
                                                         a!102)))
                                (a!285 (or (not ((_ is SomeCSPSrc)
                                                  (csp_script_src a!247)))
                                           (not a!248)
                                           (and a!283
                                                ((_ is SomeOrigin)
                                                  (ite a!249 a!250 a!256))
                                                a!284)))
                                (a!303 (wd_document (ite (= a!299 0)
                                                         (@0ArrayWindow (windows P))
                                                         a!302))))
                          (let ((a!105 (ite (c_csp_inherit_local_from_initiator
                                              (config L1))
                                            (= (rp_hd_csp (rp_headers R1))
                                               (rp_hd_csp (dc_headers a!103)))
                                            a!104))
                                (a!305 (ite (c_csp_inherit_local_from_initiator
                                              (config P))
                                            (= (rp_hd_csp (rp_headers V))
                                               (rp_hd_csp (dc_headers a!303)))
                                            a!304)))
                          (let ((a!116 (ite (c_csp_inherit_blob_from_creator
                                              (config L1))
                                            (= (rp_hd_csp (rp_headers R1))
                                               a!115)
                                            (ite a!98 a!105 a!104)))
                                (a!316 (ite (c_csp_inherit_blob_from_creator
                                              (config P))
                                            (= (rp_hd_csp (rp_headers V)) a!315)
                                            (ite a!298 a!305 a!304))))
                          (let ((a!117 (and a!116
                                            ((_ is SomeBlob)
                                              (ite a!106
                                                   (@0ArrayoptionBlob K1)
                                                   a!114))))
                                (a!317 (and a!316
                                            ((_ is SomeBlob)
                                              (ite a!306
                                                   (@0ArrayoptionBlob O)
                                                   a!314)))))
                          (let ((a!118 (ite ((_ is url_path_blob)
                                              (url_path (rp_url R1)))
                                            a!117
                                            (ite a!98 a!105 a!104)))
                                (a!318 (ite ((_ is url_path_blob)
                                              (url_path (rp_url V)))
                                            a!317
                                            (ite a!298 a!305 a!304))))
                          (let ((a!119 (ite ((_ is url_path_data)
                                              (url_path (rp_url R1)))
                                            (ite a!98 a!105 a!104)
                                            a!118))
                                (a!319 (ite ((_ is url_path_data)
                                              (url_path (rp_url V)))
                                            (ite a!298 a!305 a!304)
                                            a!318)))
                          (let ((a!120 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url R1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url R1)))
                                           a!119))
                                (a!320 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url V)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url V)))
                                           a!319)))
                          (let ((a!153 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            (and a!85 (= a!86 P1))
                                            (and a!120 a!152)))
                                (a!353 (ite ((_ is ContentElementScript)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            (and a!285 (= a!286 T))
                                            (and a!320 a!352))))
                          (let ((a!154 (or ((_ is ContentElementImage)
                                             (@0SomeContentElement
                                               (rp_content R1)))
                                           ((_ is ContentElementHTML)
                                             (@0SomeContentElement
                                               (rp_content R1)))
                                           a!153))
                                (a!354 (or ((_ is ContentElementImage)
                                             (@0SomeContentElement
                                               (rp_content V)))
                                           ((_ is ContentElementHTML)
                                             (@0SomeContentElement
                                               (rp_content V)))
                                           a!353)))
                          (let ((a!191 (and (or ((_ is ResponseOk) (rp_code R1))
                                                a!3)
                                            (or ((_ is EmitterClient)
                                                  (ft_emitter N1))
                                                a!4)
                                            a!16
                                            (= A2 P1)
                                            (ite ((_ is DOMTopLevel) Q1)
                                                 a!46
                                                 (and a!154
                                                      a!168
                                                      a!169
                                                      (= O1 a!184)
                                                      a!185))
                                            (= D2 O1)
                                            (= H1 S1)
                                            a!189
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
                                            a!190
                                            (= W1 K1)))
                                (a!407 (and (or ((_ is ResponseOk) (rp_code V))
                                                a!193)
                                            (or ((_ is EmitterClient)
                                                  (ft_emitter R))
                                                a!194)
                                            a!206
                                            (= A2 A1)
                                            (= A1 T)
                                            (= (@0ContentElementFrame a!217) D1)
                                            (= (@1ContentElementFrame a!217) F1)
                                            (not ((_ is ContentElementScript)
                                                   a!217))
                                            (ite ((_ is DOMTopLevel) U)
                                                 a!246
                                                 (and a!354
                                                      a!368
                                                      a!369
                                                      (= S a!384)
                                                      a!385))
                                            (not ((_ is ContentElementImage)
                                                   a!217))
                                            (not ((_ is ContentElementHTML)
                                                   a!217))
                                            (not a!386)
                                            ((_ is SomeDOMElement)
                                              (ite (= B1 0) a!207 a!216))
                                            (= D2 Z)
                                            (= H1 G1)
                                            (= Z a!393)
                                            (= Y S)
                                            (= I W)
                                            a!397
                                            a!401
                                            a!405
                                            (= Y1 H)
                                            (= N (DOMPath J K))
                                            (= N (DOMPath nilInt U))
                                            (= H (DOMPath (consInt B1 J) K))
                                            (= X1 X)
                                            (= X P)
                                            (= (ft_response R) (SomeResponse V))
                                            (= (rp_code V) ResponseOk)
                                            (= B2 M)
                                            (= M R)
                                            (= I1 C1)
                                            (= C1 V)
                                            ((_ is SomeContentElement)
                                              (rp_content V))
                                            a!406
                                            (= W1 L)
                                            (= L O))))
                          (let ((a!423 (and (Reachable X1 Z1 A)
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
                                            (or a!191 a!407)
                                            a!421
                                            a!422
                                            (= C
                                               (consEvent (EvDOMUpdate Y1) Z1)))))
                            (=> a!423 (Reachable X1 C B)))))))))))))))))))))
                          :weight 0))))
      (a!4 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 21 22))
                      (SomeInt 48)
                      (url_path_res (anypath 49))))
      (a!5 (Build_RequestHeaders
             NoneOrigin
             (Build_ArrayoptionCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping
               NoneCookieMapping)
             NoneURL))
      (a!6 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 21 22))
                      (SomeInt 48)
                      (url_path_res (anypath 86))))
      (a!7 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 21 22))
                      (SomeInt 74)
                      (url_path_res (anypath 72))))
      (a!8 (Build_ArrayoptionCookieMapping
             NoneCookieMapping
             NoneCookieMapping
             NoneCookieMapping
             (SomeCookieMapping (Build_CookieMapping (NoPrefix 70) 75))
             NoneCookieMapping
             NoneCookieMapping
             NoneCookieMapping
             NoneCookieMapping))
      (a!9 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 21 22))
                      (SomeInt 56)
                      (url_path_res (anypath 57))))
      (a!10 (url_path_blob (TupleOrigin ProtocolHTTP
                                        (SomeDomain (subdomain 21 22))
                                        (SomeInt 48))
                           2))
      (a!12 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                      (SomeoptionInt (SomeInt 21))
                                      22
                                      NoneInt
                                      NonePath)))
      (a!13 (SomeTrustedTypes (Build_TrustedTypes
                                (SomeoptionInt (SomeInt 53))
                                false)))
      (a!15 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 58)
                                                  (url_path_data 59 60)))))
      (a!16 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 61)
                                                  (url_path_data 62 63)))))
      (a!17 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 64)
                                                   (url_path_data 65 66)))))
      (a!18 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 67)
                                                  (url_path_data 68 69)))))
      (a!20 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 (SomeoptionInt NoneInt)
                                                 22
                                                 NoneInt
                                                 NonePath))
                       NoneTrustedTypes))
      (a!22 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 112)
                                                  (url_path_data 113 114)))))
      (a!23 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 115)
                                                  (url_path_data 116 117)))))
      (a!24 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 118)
                                                  (url_path_data 119 120)))))
      (a!25 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 121)
                                                  (url_path_data 122 123)))))
      (a!26 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 124)
                                                   (url_path_data 125 126)))))
      (a!27 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 127)
                                                  (url_path_data 128 129)))))
      (a!28 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 109)
                                                  (url_path_data 110 111)))))
      (a!31 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 NoneoptionInt
                                                 100
                                                 (SomeInt 101)
                                                 NonePath))
                       (SomeTrustedTypes (Build_TrustedTypes
                                           NoneoptionInt
                                           false))))
      (a!34 (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                            71
                                            NoneDomain
                                            (subdomain 21 22)
                                            (anypath 72)
                                            false
                                            false
                                            SSStrict)))
      (a!35 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 NoneoptionInt
                                                 95
                                                 (SomeInt 96)
                                                 NonePath))
                       NoneTrustedTypes))
      (a!38 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 69299)
                                              19483
                                              NoneDomain
                                              (domain 69843)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 68628))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 69426)
                                  (url_path_data 69841 69842)))
              NoneCSP
              NoneReferrerPolicy))
      (a!39 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 69038
                            69039
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!41 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 46474)
                                                  (url_path_data 51817 51818)))))
      (a!42 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 47350)
                                                  (url_path_data 45324 45325)))))
      (a!43 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 42965)
                                                  (url_path_data 65937 65938)))))
      (a!44 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 41304)
                                                   (url_path_data 59279 59280)))))
      (a!45 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 58483)
                                                   (url_path_data 64739 64740)))))
      (a!46 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 38025)
                                                   (url_path_data 49543 49544)))))
      (a!49 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 69180)
                                  (url_path_data 70021 70022)))
              NoneCSP
              NoneReferrerPolicy))
      (a!50 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 70363
                            70364
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!51 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 69743)
                                              19484
                                              NoneDomain
                                              (domain 69507)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 43848))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 70480)
                                  (url_path_data 69620 69621)))
              NoneCSP
              NoneReferrerPolicy))
      (a!52 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 70428
                            70429
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!55 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 72723)
                                                    (url_path_data 74376 74377))
                                         69193)))
      (a!56 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 72512)
                                                    (url_path_data 72935 72936))
                                         69719)))
      (a!57 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 58)
                                                   (url_path_data 59 60)))))
      (a!58 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 61)
                                                   (url_path_data 62 63)))))
      (a!59 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 67)
                                                   (url_path_data 68 69)))))
      (a!60 (Build_Initiators NoneInt
                              (Build_ArrayoptionInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt)))
      (a!65 (Build_Initiators NoneInt
                              (Build_ArrayoptionInt
                                (SomeInt 5)
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt
                                NoneInt)))
      (a!69 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 73999)
                                                   (url_path_data 75143 75144)))))
      (a!70 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 73366)
                                                   (url_path_data 74530 74531)))))
      (a!71 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 72495)
                                                   (url_path_data 73603 73604)))))
      (a!72 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 72346)
                                                   (url_path_data 74267 74268)))))
      (a!73 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 72251)
                                                   (url_path_data 74817 74818)))))
      (a!74 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 73445)
                                                   (url_path_data 72715 72716)))))
      (a!75 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 72354)
                                                   (url_path_data 72668 72669)))))
      (a!79 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 112)
                                                   (url_path_data 113 114)))))
      (a!81 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 115)
                                                   (url_path_data 116 117)))))
      (a!82 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 118)
                                                   (url_path_data 119 120)))))
      (a!83 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 121)
                                                   (url_path_data 122 123)))))
      (a!84 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 127)
                                                   (url_path_data 128 129)))))
      (a!85 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 109)
                                                   (url_path_data 110 111)))))
      (a!87 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 46474)
                                                   (url_path_data 51817 51818)))))
      (a!88 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 47350)
                                                   (url_path_data 45324 45325)))))
      (a!89 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 42965)
                                                   (url_path_data 65937 65938)))))
      (a!93 (Build_ArrayContentElement
              (ContentElementHTML
                (Build_HTML 35766
                            35767
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 24911
                            24912
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 24905
                            24906
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 38455
                            38456
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 41186
                            41187
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 62703
                            62704
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 20372
                            20373
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 21962
                            21963
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!94 (pairOriginoptionCSP
              (TupleOrigin ProtocolHTTP (SomeDomain (domain 0)) (SomeInt 0))
              NoneCSP))
      (a!108 (Build_ArrayoptionprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 0))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 1))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 2) 2))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 3) 3))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 6) 5))
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt))
      (a!110 (Build_ServiceWorker
               0
               (Build_ArrayoptionInt
                 NoneInt
                 NoneInt
                 NoneInt
                 NoneInt
                 NoneInt
                 NoneInt
                 NoneInt
                 NoneInt)))
      (a!117 (asserted (forall ((A Script)
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
                         (! (let ((a!1 (ite (= C4 5)
                                            (@5ArrayResponse (responses L3))
                                            (ite (= C4 6)
                                                 (@6ArrayResponse (responses L3))
                                                 (@defaultArrayResponse
                                                   (responses L3)))))
                                  (a!6 (SomeprodprodEmitterIntInt
                                         (pairprodEmitterIntInt
                                           (pairEmitterInt (ft_emitter D4) B4)
                                           C4)))
                                  (a!16 (ite (= B4 5)
                                             (@5ArrayRequest (requests L3))
                                             (ite (= B4 6)
                                                  (@6ArrayRequest (requests L3))
                                                  (@defaultArrayRequest
                                                    (requests L3)))))
                                  (a!20 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!21 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!22 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!23 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!24 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!25 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!26 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!27 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!32 (ite (= (frame_window J1) 5)
                                             (@5ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 6)
                                                  (@6ArrayWindow (windows O1))
                                                  (@defaultArrayWindow
                                                    (windows O1)))))
                                  (a!38 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!39 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!40 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!41 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!42 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!43 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!44 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!45 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!51 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!52 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!53 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!54 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!55 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!56 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!57 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!58 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!63 (ite (= (frame_window G) 5)
                                             (@5ArrayWindow (windows L))
                                             (ite (= (frame_window G) 6)
                                                  (@6ArrayWindow (windows L))
                                                  (@defaultArrayWindow
                                                    (windows L)))))
                                  (a!69 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!70 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!71 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!72 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!73 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!74 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!75 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!76 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!82 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!83 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!84 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!85 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!86 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!87 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!88 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!89 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!94 (ite (= (frame_window O2) 5)
                                             (@5ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 6)
                                                  (@6ArrayWindow (windows T2))
                                                  (@defaultArrayWindow
                                                    (windows T2)))))
                                  (a!100 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!101 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!102 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!103 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!104 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!105 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!106 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!107 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document J3)))))
                                  (a!112 (ite (= H2 5)
                                              (@5ArrayEmitter (emitters L3))
                                              (ite (= H2 6)
                                                   (@6ArrayEmitter (emitters L3))
                                                   (@defaultArrayEmitter
                                                     (emitters L3)))))
                                  (a!119 (ite (= B4 5)
                                              (@5ArrayInt (server_responses L3))
                                              (ite (= B4 6)
                                                   (@6ArrayInt (server_responses L3))
                                                   (@defaultArrayInt (server_responses L3)))))
                                  (a!136 (ite (= W3 5)
                                              (@5ArrayContentElement
                                                (data_urls L3))
                                              (ite (= W3 6)
                                                   (@6ArrayContentElement
                                                     (data_urls L3))
                                                   (@defaultArrayContentElement
                                                     (data_urls L3)))))
                                  (a!140 (ite (= Y3 4)
                                              (@4ArrayoptionBlob M4)
                                              (ite (= Y3 5)
                                                   (@5ArrayoptionBlob M4)
                                                   (ite (= Y3 6)
                                                        (@6ArrayoptionBlob M4)
                                                        (@defaultArrayoptionBlob
                                                          M4)))))
                                  (a!146 (ite (= R3 5)
                                              (@5ArrayContentElement
                                                (data_urls L3))
                                              (ite (= R3 6)
                                                   (@6ArrayContentElement
                                                     (data_urls L3))
                                                   (@defaultArrayContentElement
                                                     (data_urls L3)))))
                                  (a!150 (ite (= T3 4)
                                              (@4ArrayoptionBlob M4)
                                              (ite (= T3 5)
                                                   (@5ArrayoptionBlob M4)
                                                   (ite (= T3 6)
                                                        (@6ArrayoptionBlob M4)
                                                        (@defaultArrayoptionBlob
                                                          M4)))))
                                  (a!155 (or ((_ is ProtocolHTTPS)
                                               (url_protocol (wd_location N3)))
                                             ((_ is ProtocolHTTP)
                                               (url_protocol (wd_location N3)))))
                                  (a!156 (SomeOrigin (TupleOrigin (url_protocol (wd_location N3))
                                                                  (url_host (wd_location N3))
                                                                  (url_port (wd_location N3)))))
                                  (a!157 (OpaqueOrigin (@0url_path_data (url_path (wd_location N3)))))
                                  (a!159 (SomeOrigin (@0url_path_blob (url_path (wd_location N3)))))
                                  (a!179 (ite (= E4 4)
                                              (@4ArrayoptionSetCookie G4)
                                              (ite (= E4 5)
                                                   (@5ArrayoptionSetCookie G4)
                                                   (ite (= E4 6)
                                                        (@6ArrayoptionSetCookie
                                                          G4)
                                                        (@defaultArrayoptionSetCookie
                                                          G4)))))
                                  (a!181 (ite (= E4 5)
                                              (Build_ArrayoptionSetCookie
                                                (@0ArrayoptionSetCookie G4)
                                                (@1ArrayoptionSetCookie G4)
                                                (@2ArrayoptionSetCookie G4)
                                                (@3ArrayoptionSetCookie G4)
                                                (@4ArrayoptionSetCookie G4)
                                                (SomeSetCookie F4)
                                                (@6ArrayoptionSetCookie G4)
                                                (@defaultArrayoptionSetCookie
                                                  G4))
                                              (ite (= E4 6)
                                                   (Build_ArrayoptionSetCookie
                                                     (@0ArrayoptionSetCookie G4)
                                                     (@1ArrayoptionSetCookie G4)
                                                     (@2ArrayoptionSetCookie G4)
                                                     (@3ArrayoptionSetCookie G4)
                                                     (@4ArrayoptionSetCookie G4)
                                                     (@5ArrayoptionSetCookie G4)
                                                     (SomeSetCookie F4)
                                                     (@defaultArrayoptionSetCookie
                                                       G4))
                                                   G4)))
                                  (a!185 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!186 (= (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!187 (= (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!189 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!190 (= (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!191 (= (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!193 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!194 (= (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!195 (= (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!197 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!198 (= (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!199 (= (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!201 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!202 (= (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!203 (= (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!205 (= (sc_reg_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!206 (= (sc_path (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!207 (= (sc_name (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!209 (= (sc_reg_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!210 (= (sc_path (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!211 (= (sc_name (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4)))
                                  (a!213 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                              H4)))
                                            (sc_reg_domain F4)))
                                  (a!214 (= (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        H4)))
                                            (sc_path F4)))
                                  (a!215 (= (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        H4)))
                                            (sc_name F4))))
                            (let ((a!2 (ite (= C4 3)
                                            (@3ArrayResponse (responses L3))
                                            (ite (= C4 4)
                                                 (@4ArrayResponse (responses L3))
                                                 a!1)))
                                  (a!7 (ite (= (ft_correlator D4) 6)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@5ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              a!6
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history D4)))
                                            (ft_history D4)))
                                  (a!17 (ite (= B4 3)
                                             (@3ArrayRequest (requests L3))
                                             (ite (= B4 4)
                                                  (@4ArrayRequest (requests L3))
                                                  a!16)))
                                  (a!28 (ite (= G1 4)
                                             a!24
                                             (ite (= G1 5)
                                                  a!25
                                                  (ite (= G1 6) a!26 a!27))))
                                  (a!33 (ite (= (frame_window J1) 3)
                                             (@3ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 4)
                                                  (@4ArrayWindow (windows O1))
                                                  a!32)))
                                  (a!46 (ite (= D2 4)
                                             a!42
                                             (ite (= D2 5)
                                                  a!43
                                                  (ite (= D2 6) a!44 a!45))))
                                  (a!59 (ite (= D 4)
                                             a!55
                                             (ite (= D 5)
                                                  a!56
                                                  (ite (= D 6) a!57 a!58))))
                                  (a!64 (ite (= (frame_window G) 3)
                                             (@3ArrayWindow (windows L))
                                             (ite (= (frame_window G) 4)
                                                  (@4ArrayWindow (windows L))
                                                  a!63)))
                                  (a!77 (ite (= A1 4)
                                             a!73
                                             (ite (= A1 5)
                                                  a!74
                                                  (ite (= A1 6) a!75 a!76))))
                                  (a!90 (ite (= L2 4)
                                             a!86
                                             (ite (= L2 5)
                                                  a!87
                                                  (ite (= L2 6) a!88 a!89))))
                                  (a!95 (ite (= (frame_window O2) 3)
                                             (@3ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 4)
                                                  (@4ArrayWindow (windows T2))
                                                  a!94)))
                                  (a!108 (ite (= I3 4)
                                              a!104
                                              (ite (= I3 5)
                                                   a!105
                                                   (ite (= I3 6) a!106 a!107))))
                                  (a!113 (ite (= H2 3)
                                              (@3ArrayEmitter (emitters L3))
                                              (ite (= H2 4)
                                                   (@4ArrayEmitter (emitters L3))
                                                   a!112)))
                                  (a!120 (ite (= B4 3)
                                              (@3ArrayInt (server_responses L3))
                                              (ite (= B4 4)
                                                   (@4ArrayInt (server_responses L3))
                                                   a!119)))
                                  (a!137 (ite (= W3 3)
                                              (@3ArrayContentElement
                                                (data_urls L3))
                                              (ite (= W3 4)
                                                   (@4ArrayContentElement
                                                     (data_urls L3))
                                                   a!136)))
                                  (a!141 (ite (= Y3 1)
                                              (@1ArrayoptionBlob M4)
                                              (ite (= Y3 2)
                                                   (@2ArrayoptionBlob M4)
                                                   (ite (= Y3 3)
                                                        (@3ArrayoptionBlob M4)
                                                        a!140))))
                                  (a!147 (ite (= R3 3)
                                              (@3ArrayContentElement
                                                (data_urls L3))
                                              (ite (= R3 4)
                                                   (@4ArrayContentElement
                                                     (data_urls L3))
                                                   a!146)))
                                  (a!151 (ite (= T3 1)
                                              (@1ArrayoptionBlob M4)
                                              (ite (= T3 2)
                                                   (@2ArrayoptionBlob M4)
                                                   (ite (= T3 3)
                                                        (@3ArrayoptionBlob M4)
                                                        a!150))))
                                  (a!158 (ite ((_ is url_path_data)
                                                (url_path (wd_location N3)))
                                              (SomeOrigin a!157)
                                              NoneOrigin))
                                  (a!160 (ite ((_ is url_path_blob)
                                                (url_path (wd_location N3)))
                                              a!159
                                              NoneOrigin))
                                  (a!180 (ite (= E4 1)
                                              (@1ArrayoptionSetCookie G4)
                                              (ite (= E4 2)
                                                   (@2ArrayoptionSetCookie G4)
                                                   (ite (= E4 3)
                                                        (@3ArrayoptionSetCookie
                                                          G4)
                                                        a!179))))
                                  (a!182 (ite (= E4 3)
                                              (Build_ArrayoptionSetCookie
                                                (@0ArrayoptionSetCookie G4)
                                                (@1ArrayoptionSetCookie G4)
                                                (@2ArrayoptionSetCookie G4)
                                                (SomeSetCookie F4)
                                                (@4ArrayoptionSetCookie G4)
                                                (@5ArrayoptionSetCookie G4)
                                                (@6ArrayoptionSetCookie G4)
                                                (@defaultArrayoptionSetCookie
                                                  G4))
                                              (ite (= E4 4)
                                                   (Build_ArrayoptionSetCookie
                                                     (@0ArrayoptionSetCookie G4)
                                                     (@1ArrayoptionSetCookie G4)
                                                     (@2ArrayoptionSetCookie G4)
                                                     (@3ArrayoptionSetCookie G4)
                                                     (SomeSetCookie F4)
                                                     (@5ArrayoptionSetCookie G4)
                                                     (@6ArrayoptionSetCookie G4)
                                                     (@defaultArrayoptionSetCookie
                                                       G4))
                                                   a!181)))
                                  (a!188 (ite (and a!185 a!186 a!187)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!192 (ite (and a!189 a!190 a!191)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!196 (ite (and a!193 a!194 a!195)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!200 (ite (and a!197 a!198 a!199)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!204 (ite (and a!201 a!202 a!203)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!208 (ite (and a!205 a!206 a!207)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!212 (ite (and a!209 a!210 a!211)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!216 (ite (and a!213 a!214 a!215)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                H4))))))
                            (let ((a!3 (ite (= C4 1)
                                            (@1ArrayResponse (responses L3))
                                            (ite (= C4 2)
                                                 (@2ArrayResponse (responses L3))
                                                 a!2)))
                                  (a!8 (ite (= (ft_correlator D4) 5)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              a!6
                                              (@6ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history D4)))
                                            a!7))
                                  (a!18 (ite (= B4 1)
                                             (@1ArrayRequest (requests L3))
                                             (ite (= B4 2)
                                                  (@2ArrayRequest (requests L3))
                                                  a!17)))
                                  (a!29 (ite (= G1 1)
                                             a!21
                                             (ite (= G1 2)
                                                  a!22
                                                  (ite (= G1 3) a!23 a!28))))
                                  (a!34 (ite (= (frame_window J1) 1)
                                             (@1ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 2)
                                                  (@2ArrayWindow (windows O1))
                                                  a!33)))
                                  (a!47 (ite (= D2 1)
                                             a!39
                                             (ite (= D2 2)
                                                  a!40
                                                  (ite (= D2 3) a!41 a!46))))
                                  (a!60 (ite (= D 1)
                                             a!52
                                             (ite (= D 2)
                                                  a!53
                                                  (ite (= D 3) a!54 a!59))))
                                  (a!65 (ite (= (frame_window G) 1)
                                             (@1ArrayWindow (windows L))
                                             (ite (= (frame_window G) 2)
                                                  (@2ArrayWindow (windows L))
                                                  a!64)))
                                  (a!78 (ite (= A1 1)
                                             a!70
                                             (ite (= A1 2)
                                                  a!71
                                                  (ite (= A1 3) a!72 a!77))))
                                  (a!91 (ite (= L2 1)
                                             a!83
                                             (ite (= L2 2)
                                                  a!84
                                                  (ite (= L2 3) a!85 a!90))))
                                  (a!96 (ite (= (frame_window O2) 1)
                                             (@1ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 2)
                                                  (@2ArrayWindow (windows T2))
                                                  a!95)))
                                  (a!109 (ite (= I3 1)
                                              a!101
                                              (ite (= I3 2)
                                                   a!102
                                                   (ite (= I3 3) a!103 a!108))))
                                  (a!114 (ite (= H2 1)
                                              (@1ArrayEmitter (emitters L3))
                                              (ite (= H2 2)
                                                   (@2ArrayEmitter (emitters L3))
                                                   a!113)))
                                  (a!121 (ite (= B4 1)
                                              (@1ArrayInt (server_responses L3))
                                              (ite (= B4 2)
                                                   (@2ArrayInt (server_responses L3))
                                                   a!120)))
                                  (a!138 (ite (= W3 1)
                                              (@1ArrayContentElement
                                                (data_urls L3))
                                              (ite (= W3 2)
                                                   (@2ArrayContentElement
                                                     (data_urls L3))
                                                   a!137)))
                                  (a!148 (ite (= R3 1)
                                              (@1ArrayContentElement
                                                (data_urls L3))
                                              (ite (= R3 2)
                                                   (@2ArrayContentElement
                                                     (data_urls L3))
                                                   a!147)))
                                  (a!161 (ite ((_ is url_path_data)
                                                (url_path (wd_location N3)))
                                              NoneOrigin
                                              a!160))
                                  (a!183 (ite (= E4 1)
                                              (Build_ArrayoptionSetCookie
                                                (@0ArrayoptionSetCookie G4)
                                                (SomeSetCookie F4)
                                                (@2ArrayoptionSetCookie G4)
                                                (@3ArrayoptionSetCookie G4)
                                                (@4ArrayoptionSetCookie G4)
                                                (@5ArrayoptionSetCookie G4)
                                                (@6ArrayoptionSetCookie G4)
                                                (@defaultArrayoptionSetCookie
                                                  G4))
                                              (ite (= E4 2)
                                                   (Build_ArrayoptionSetCookie
                                                     (@0ArrayoptionSetCookie G4)
                                                     (@1ArrayoptionSetCookie G4)
                                                     (SomeSetCookie F4)
                                                     (@3ArrayoptionSetCookie G4)
                                                     (@4ArrayoptionSetCookie G4)
                                                     (@5ArrayoptionSetCookie G4)
                                                     (@6ArrayoptionSetCookie G4)
                                                     (@defaultArrayoptionSetCookie
                                                       G4))
                                                   a!182)))
                                  (a!217 (Build_ArrayoptionSetCookie
                                           (ite ((_ is SomeSetCookie)
                                                  (@0ArrayoptionSetCookie H4))
                                                a!188
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@1ArrayoptionSetCookie H4))
                                                a!192
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@2ArrayoptionSetCookie H4))
                                                a!196
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@3ArrayoptionSetCookie H4))
                                                a!200
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@4ArrayoptionSetCookie H4))
                                                a!204
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@5ArrayoptionSetCookie H4))
                                                a!208
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@6ArrayoptionSetCookie H4))
                                                a!212
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@defaultArrayoptionSetCookie
                                                    H4))
                                                a!216
                                                NoneSetCookie))))
                            (let ((a!4 (EvResponse (ite (= C4 0)
                                                        (@0ArrayResponse (responses L3))
                                                        a!3)
                                                   (ft_correlator D4)))
                                  (a!5 (SomeResponse (ite (= C4 0)
                                                          (@0ArrayResponse (responses L3))
                                                          a!3)))
                                  (a!9 (ite (= (ft_correlator D4) 4)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              a!6
                                              (@5ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@6ArrayoptionprodprodEmitterIntInt
                                                (ft_history D4))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history D4)))
                                            a!8))
                                  (a!15 (rp_url (ite (= C4 0)
                                                     (@0ArrayResponse (responses L3))
                                                     a!3)))
                                  (a!19 (= (ft_request D4)
                                           (ite (= B4 0)
                                                (@0ArrayRequest (requests L3))
                                                a!18)))
                                  (a!30 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= G1 0)
                                                                 a!20
                                                                 a!29))))
                                  (a!31 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= G1 0)
                                                                 a!20
                                                                 a!29))))
                                  (a!35 (= (ite (= (frame_window J1) 0)
                                                (@0ArrayWindow (windows O1))
                                                a!34)
                                           M1))
                                  (a!48 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= D2 0)
                                                                 a!38
                                                                 a!47))))
                                  (a!49 (@0DOMElementForm (@0SomeDOMElement (ite (= D2
                                                                                    0)
                                                                                 a!38
                                                                                 a!47))))
                                  (a!61 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= D 0)
                                                                 a!51
                                                                 a!60))))
                                  (a!62 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= D 0)
                                                                 a!51
                                                                 a!60))))
                                  (a!66 (= (ite (= (frame_window G) 0)
                                                (@0ArrayWindow (windows L))
                                                a!65)
                                           J))
                                  (a!79 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= A1 0)
                                                                 a!69
                                                                 a!78))))
                                  (a!80 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= A1 0)
                                                                 a!69
                                                                 a!78))))
                                  (a!92 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= L2 0)
                                                                 a!82
                                                                 a!91))))
                                  (a!93 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= L2 0)
                                                                 a!82
                                                                 a!91))))
                                  (a!97 (= (ite (= (frame_window O2) 0)
                                                (@0ArrayWindow (windows T2))
                                                a!96)
                                           R2))
                                  (a!110 (@1DOMElementResource
                                           (@0SomeDOMElement (ite (= I3 0)
                                                                  a!100
                                                                  a!109))))
                                  (a!111 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= I3 0)
                                                                  a!100
                                                                  a!109))))
                                  (a!115 (= (ite (= H2 0)
                                                 (@0ArrayEmitter (emitters L3))
                                                 a!114)
                                            (EmitterScript J2 I2)))
                                  (a!118 (rq_url (ite (= B4 0)
                                                      (@0ArrayRequest (requests L3))
                                                      a!18)))
                                  (a!122 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            0))
                                  (a!123 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            1))
                                  (a!124 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            2))
                                  (a!125 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            3))
                                  (a!126 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            4))
                                  (a!127 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            5))
                                  (a!128 (= (ite (= B4 0)
                                                 (@0ArrayInt (server_responses L3))
                                                 a!121)
                                            6))
                                  (a!135 (rp_content (ite (= C4 0)
                                                          (@0ArrayResponse (responses L3))
                                                          a!3)))
                                  (a!139 (SomeContentElement
                                           (ite (= W3 0)
                                                (@0ArrayContentElement
                                                  (data_urls L3))
                                                a!138)))
                                  (a!144 (rp_headers (ite (= C4 0)
                                                          (@0ArrayResponse (responses L3))
                                                          a!3)))
                                  (a!145 (rp_code (ite (= C4 0)
                                                       (@0ArrayResponse (responses L3))
                                                       a!3)))
                                  (a!149 (SomeContentElement
                                           (ite (= R3 0)
                                                (@0ArrayContentElement
                                                  (data_urls L3))
                                                a!148)))
                                  (a!162 (ite ((_ is ProtocolData)
                                                (url_protocol (wd_location N3)))
                                              a!158
                                              a!161))
                                  (a!184 (= L4
                                            (ite (= E4 0)
                                                 (Build_ArrayoptionSetCookie
                                                   (SomeSetCookie F4)
                                                   (@1ArrayoptionSetCookie G4)
                                                   (@2ArrayoptionSetCookie G4)
                                                   (@3ArrayoptionSetCookie G4)
                                                   (@4ArrayoptionSetCookie G4)
                                                   (@5ArrayoptionSetCookie G4)
                                                   (@6ArrayoptionSetCookie G4)
                                                   (@defaultArrayoptionSetCookie
                                                     G4))
                                                 a!183))))
                            (let ((a!10 (ite (= (ft_correlator D4) 3)
                                             (Build_ArrayoptionprodprodEmitterIntInt
                                               (@0ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@1ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@2ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               a!6
                                               (@4ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@5ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@6ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@defaultArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4)))
                                             a!9))
                                  (a!36 (and (= (@0ContentElementFrame a!30) J1)
                                             (= (@1ContentElementFrame a!30) I1)
                                             (not ((_ is ContentElementScript)
                                                    a!30))
                                             (not ((_ is ContentElementImage)
                                                    a!30))
                                             (not ((_ is ContentElementHTML)
                                                    a!30))
                                             (not a!31)
                                             ((_ is SomeDOMElement)
                                               (ite (= G1 0) a!20 a!29))
                                             (= E2 N1)
                                             (= N1 S1)
                                             (= U1 H1)
                                             (= S1 T1)
                                             (= M1 T1)
                                             a!35
                                             (= F1 (DOMPath (consInt G1 K1) L1))
                                             (= B2 F1)
                                             (= Q1 (DOMPath K1 L1))
                                             (= Q1 (DOMPath nilInt R1))
                                             (= V1 O1)
                                             (= O1 P1)))
                                  (a!67 (and (= (@0ContentElementFrame a!61) G)
                                             (= (@1ContentElementFrame a!61) F)
                                             (not ((_ is ContentElementScript)
                                                    a!61))
                                             (not ((_ is ContentElementImage)
                                                    a!61))
                                             (not ((_ is ContentElementHTML)
                                                    a!61))
                                             (not a!62)
                                             ((_ is SomeDOMElement)
                                               (ite (= D 0) a!51 a!60))
                                             (= P Q)
                                             (= K P)
                                             (= B1 K)
                                             (= J Q)
                                             (= R E)
                                             a!66
                                             (= C (DOMPath (consInt D H) I))
                                             (= Y C)
                                             (= N (DOMPath H I))
                                             (= N (DOMPath nilInt O))
                                             (= S L)
                                             (= L M)))
                                  (a!98 (and (= (@0ContentElementFrame a!92) O2)
                                             (= (@1ContentElementFrame a!92) N2)
                                             (not ((_ is ContentElementScript)
                                                    a!92))
                                             (not ((_ is ContentElementImage)
                                                    a!92))
                                             (not ((_ is ContentElementHTML)
                                                    a!92))
                                             (not a!93)
                                             ((_ is SomeDOMElement)
                                               (ite (= L2 0) a!82 a!91))
                                             (= Z2 M2)
                                             (= S2 X2)
                                             (= R2 Y2)
                                             (= J3 S2)
                                             (= X2 Y2)
                                             a!97
                                             (= V2 (DOMPath P2 Q2))
                                             (= V2 (DOMPath nilInt W2))
                                             (= K2 (DOMPath (consInt L2 P2) Q2))
                                             (= G3 K2)
                                             (= T2 U2)
                                             (= A3 T2)))
                                  (a!129 (ite a!127
                                              (@5ArrayResponse (responses L3))
                                              (ite a!128
                                                   (@6ArrayResponse (responses L3))
                                                   (@defaultArrayResponse
                                                     (responses L3)))))
                                  (a!142 (and (= (blob_origin A4) Z3)
                                              (= a!15 (blob_url A4))
                                              (= (url_path a!15)
                                                 (url_path_blob Z3 Y3))
                                              (= (ite (= Y3 0)
                                                      (@0ArrayoptionBlob M4)
                                                      a!141)
                                                 (SomeBlob A4))
                                              (= a!135
                                                 (SomeContentElement
                                                   (blob_celt A4)))))
                                  (a!152 (and (= (blob_origin V3) U3)
                                              (= a!15 (blob_url V3))
                                              (= (url_path a!15)
                                                 (url_path_blob U3 T3))
                                              (= (ite (= T3 0)
                                                      (@0ArrayoptionBlob M4)
                                                      a!151)
                                                 (SomeBlob V3))
                                              (= a!135
                                                 (SomeContentElement
                                                   (blob_celt V3)))))
                                  (a!163 (= (SomeOrigin (@0SomeOrigin (rp_hd_access_control_allow_origin
                                                                        a!144)))
                                            (ite a!155 a!156 a!162)))
                                  (a!166 (or ((_ is SSLax) (sc_same_site F4))
                                             ((_ is SSStrict) (sc_same_site F4))
                                             (and (sc_secure F4)
                                                  (= (url_protocol a!15)
                                                     ProtocolHTTPS))))
                                  (a!167 (= (@0domain (@0SomeDomain (sc_domain F4)))
                                            (@0domain (@0SomeDomain (url_host a!15)))))
                                  (a!169 (= (@1subdomain (@0SomeDomain (sc_domain F4)))
                                            (@0domain (@0SomeDomain (url_host a!15)))))
                                  (a!170 (= (@0subdomain (@0SomeDomain (sc_domain F4)))
                                            (@0subdomain (@0SomeDomain (url_host a!15)))))
                                  (a!171 (= (@1subdomain (@0SomeDomain (sc_domain F4)))
                                            (@1subdomain (@0SomeDomain (url_host a!15)))))
                                  (a!177 (and (or (not (sc_secure F4))
                                                  (= (url_protocol a!15)
                                                     ProtocolHTTPS))
                                              (sc_secure F4)
                                              (not ((_ is url_path_blob)
                                                     (url_path a!15)))
                                              (not ((_ is url_path_data)
                                                     (url_path a!15)))
                                              ((_ is SomeDomain)
                                                (url_host a!15))
                                              (= (sc_reg_domain F4)
                                                 (@0SomeDomain (url_host a!15)))
                                              (= (@0url_path_res (url_path a!15))
                                                 slash)
                                              (= (sc_path F4) slash)
                                              (= (sc_domain F4) NoneDomain))))
                            (let ((a!11 (ite (= (ft_correlator D4) 2)
                                             (Build_ArrayoptionprodprodEmitterIntInt
                                               (@0ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@1ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               a!6
                                               (@3ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@4ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@5ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@6ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@defaultArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4)))
                                             a!10))
                                  (a!37 (or (and (= E2 Z1)
                                                 (= Z1 A2)
                                                 (= U1 A2)
                                                 (= X1 (DOMPath nilInt Y1))
                                                 (= B2 X1)
                                                 (= V1 W1))
                                            a!36))
                                  (a!68 (or (and (= W X)
                                                 (= B1 W)
                                                 (= R X)
                                                 (= U (DOMPath nilInt V))
                                                 (= Y U)
                                                 (= S T))
                                            a!67))
                                  (a!99 (or (and (= Z2 F3)
                                                 (= J3 E3)
                                                 (= E3 F3)
                                                 (= G3 C3)
                                                 (= C3 (DOMPath nilInt D3))
                                                 (= A3 B3))
                                            a!98))
                                  (a!130 (ite a!125
                                              (@3ArrayResponse (responses L3))
                                              (ite a!126
                                                   (@4ArrayResponse (responses L3))
                                                   a!129)))
                                  (a!143 (or (and (= X3 J4)
                                                  (= (url_path a!15)
                                                     (url_path_data X3 W3))
                                                  (= a!135 a!139))
                                             a!142))
                                  (a!153 (or (and (= S3 J4)
                                                  (= (url_path a!15)
                                                     (url_path_data S3 R3))
                                                  (= a!135 a!149))
                                             a!152))
                                  (a!164 (ite ((_ is EmitterScript)
                                                (ft_emitter D4))
                                              (or (= a!135 NoneContentElement)
                                                  a!163)
                                              (or ((_ is EmitterWorker)
                                                    (ft_emitter D4))
                                                  ((_ is EmitterForm)
                                                    (ft_emitter D4))
                                                  a!163)))
                                  (a!168 (and a!167
                                              ((_ is domain)
                                                (@0SomeDomain (url_host a!15)))))
                                  (a!172 (ite ((_ is domain)
                                                (@0SomeDomain (url_host a!15)))
                                              a!169
                                              (and a!170 a!171))))
                            (let ((a!12 (ite (= (ft_correlator D4) 1)
                                             (Build_ArrayoptionprodprodEmitterIntInt
                                               (@0ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               a!6
                                               (@2ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@3ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@4ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@5ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@6ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@defaultArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4)))
                                             a!11))
                                  (a!50 (and a!37
                                             a!48
                                             ((_ is SomeDOMElement)
                                               (ite (= D2 0) a!38 a!47))
                                             (= N3 E2)
                                             (= M3 U1)
                                             (= E1 B2)
                                             (= B2 (DOMPath C2 (DOMIndex D2)))
                                             (= L3 V1)
                                             (= D1 F2)
                                             (= a!49 F2)
                                             (= (ft_emitter D4)
                                                (EmitterForm E1 D1))))
                                  (a!81 (and a!68
                                             ((_ is ContentElementScript) a!79)
                                             (not ((_ is ContentElementImage)
                                                    a!79))
                                             (not ((_ is ContentElementHTML)
                                                    a!79))
                                             (not a!80)
                                             ((_ is SomeDOMElement)
                                               (ite (= A1 0) a!69 a!78))
                                             (= N3 B1)
                                             (= M3 R)
                                             (= B Y)
                                             (= Y (DOMPath Z (DOMIndex A1)))
                                             (= L3 S)
                                             (= A C1)
                                             (= (@0ContentElementScript a!79)
                                                C1)
                                             (= (ft_emitter D4)
                                                (EmitterScript B A))))
                                  (a!116 (and a!99
                                              ((_ is ContentElementScript)
                                                a!110)
                                              (not ((_ is ContentElementImage)
                                                     a!110))
                                              (not ((_ is ContentElementHTML)
                                                     a!110))
                                              (not a!111)
                                              ((_ is SomeDOMElement)
                                                (ite (= I3 0) a!100 a!109))
                                              (= N3 J3)
                                              (= M3 Z2)
                                              (= G3 (DOMPath H3 (DOMIndex I3)))
                                              (= J2 G3)
                                              (= L3 A3)
                                              (= I2 K3)
                                              (= (@0ContentElementScript a!110)
                                                 K3)
                                              a!115
                                              (= (ft_emitter D4)
                                                 (EmitterCORSPreflight H2 G2))))
                                  (a!131 (ite a!123
                                              (@1ArrayResponse (responses L3))
                                              (ite a!124
                                                   (@2ArrayResponse (responses L3))
                                                   a!130)))
                                  (a!165 (or ((_ is EmitterClient)
                                               (ft_emitter D4))
                                             (not ((_ is SomeOrigin)
                                                    (rp_hd_access_control_allow_origin
                                                      a!144)))
                                             a!164))
                                  (a!173 (ite ((_ is domain)
                                                (@0SomeDomain (sc_domain F4)))
                                              a!168
                                              a!172)))
                            (let ((a!13 (ite (= (ft_correlator D4) 0)
                                             (Build_ArrayoptionprodprodEmitterIntInt
                                               a!6
                                               (@1ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@2ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@3ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@4ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@5ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@6ArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4))
                                               (@defaultArrayoptionprodprodEmitterIntInt
                                                 (ft_history D4)))
                                             a!12))
                                  (a!117 (or (and (= N3 M3)
                                                  (= (ft_emitter D4)
                                                     EmitterClient))
                                             (and (= N3 M3)
                                                  (= (ft_emitter D4)
                                                     EmitterWorker))
                                             a!50
                                             a!81
                                             a!116))
                                  (a!132 (= (ite a!122
                                                 (@0ArrayResponse (responses L3))
                                                 a!131)
                                            (ite (= C4 0)
                                                 (@0ArrayResponse (responses L3))
                                                 a!3)))
                                  (a!174 (or (not ((_ is SomeDomain)
                                                    (sc_domain F4)))
                                             a!173)))
                            (let ((a!14 (= P3
                                           (Build_State (+ 1 J4)
                                                        (Build_FetchEngine
                                                          (+ 1 J4)
                                                          (ft_emitter D4)
                                                          (ft_request D4)
                                                          (ft_correlator D4)
                                                          a!5
                                                          a!13)
                                                        K4
                                                        M3
                                                        L4
                                                        M4
                                                        N4)))
                                  (a!133 (and (or ((_ is ProtocolHTTPS)
                                                    (url_protocol a!118))
                                                  ((_ is ProtocolHTTP)
                                                    (url_protocol a!118)))
                                              (= (url_protocol a!15)
                                                 ProtocolHTTP)
                                              a!132))
                                  (a!134 (and (or ((_ is ProtocolHTTPS)
                                                    (url_protocol a!118))
                                                  ((_ is ProtocolHTTP)
                                                    (url_protocol a!118)))
                                              (= (url_protocol a!15)
                                                 ProtocolHTTPS)
                                              a!132))
                                  (a!175 (and (or (not (sc_secure F4))
                                                  (= (url_protocol a!15)
                                                     ProtocolHTTPS))
                                              a!174
                                              ((_ is SomeDomain)
                                                (url_host a!15))
                                              (= (sc_reg_domain F4)
                                                 (@0SomeDomain (url_host a!15)))))
                                  (a!176 (and (or (not (sc_secure F4))
                                                  (= (url_protocol a!15)
                                                     ProtocolHTTPS))
                                              a!174
                                              (sc_secure F4)
                                              ((_ is SomeDomain)
                                                (url_host a!15))
                                              (= (sc_reg_domain F4)
                                                 (@0SomeDomain (url_host a!15))))))
                            (let ((a!154 (or a!133
                                             a!134
                                             (and a!143
                                                  (= (rp_hd_access_control_allow_origin
                                                       a!144)
                                                     NoneOrigin)
                                                  (= (rp_hd_location a!144)
                                                     NoneURL)
                                                  (= (url_protocol a!15)
                                                     ProtocolBlob)
                                                  (= a!145 ResponseOk)
                                                  (= (rp_hd_set_cookie a!144)
                                                     NoneSetCookie))
                                             (and a!153
                                                  (= (rp_hd_access_control_allow_origin
                                                       a!144)
                                                     NoneOrigin)
                                                  (= (rp_hd_location a!144)
                                                     NoneURL)
                                                  (= (url_protocol a!15)
                                                     ProtocolData)
                                                  (= a!145 ResponseOk)
                                                  (= (rp_hd_set_cookie a!144)
                                                     NoneSetCookie))))
                                  (a!178 (ite ((_ is NoPrefix) (sc_name F4))
                                              a!175
                                              (ite ((_ is Secure) (sc_name F4))
                                                   a!176
                                                   a!177))))
                            (let ((a!218 (and a!166
                                              a!178
                                              (= (rp_hd_set_cookie a!144)
                                                 (SomeSetCookie F4))
                                              (= (ite (= E4 0)
                                                      (@0ArrayoptionSetCookie
                                                        G4)
                                                      a!180)
                                                 NoneSetCookie)
                                              a!184
                                              (= G4 a!217))))
                            (let ((a!219 (or (and (= (rp_hd_set_cookie a!144)
                                                     NoneSetCookie)
                                                  (= L4 H4))
                                             a!218)))
                            (let ((a!220 (and (Reachable L3 I4 O3)
                                              (= Q3 (consEvent a!4 I4))
                                              a!14
                                              (= O3
                                                 (Build_State J4
                                                              D4
                                                              K4
                                                              M3
                                                              H4
                                                              M4
                                                              N4))
                                              (= a!15 (rq_url (ft_request D4)))
                                              a!19
                                              a!117
                                              a!154
                                              a!165
                                              a!219
                                              ((_ is NoneResponse)
                                                (ft_response D4)))))
                              (=> a!220 (Reachable L3 Q3 P3)))))))))))))))
                            :weight 0))))
      (a!118 (Build_ArrayoptionprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 0))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 1))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 2) 2))
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 3) 3))
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt))
      (a!120 (asserted (forall ((A Script)
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
                                  (a!16 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!17 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!18 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H1)))))
                                  (a!23 (ite (= (frame_window J1) 5)
                                             (@5ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 6)
                                                  (@6ArrayWindow (windows O1))
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
                                  (a!34 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!35 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!36 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E2)))))
                                  (a!42 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!43 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!44 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!45 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!46 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!47 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!48 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!49 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document E)))))
                                  (a!54 (ite (= (frame_window G) 5)
                                             (@5ArrayWindow (windows L))
                                             (ite (= (frame_window G) 6)
                                                  (@6ArrayWindow (windows L))
                                                  (@defaultArrayWindow
                                                    (windows L)))))
                                  (a!60 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!61 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!62 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!63 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!64 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!65 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!66 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document B1)))))
                                  (a!67 (@defaultArrayoptionDOMElement
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
                                  (a!78 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!79 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!80 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M2)))))
                                  (a!85 (ite (= (frame_window O2) 5)
                                             (@5ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 6)
                                                  (@6ArrayWindow (windows T2))
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
                                  (a!96 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document J3)))))
                                  (a!97 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document J3)))))
                                  (a!98 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document J3)))))
                                  (a!103 (ite (= H2 5)
                                              (@5ArrayEmitter (emitters L3))
                                              (ite (= H2 6)
                                                   (@6ArrayEmitter (emitters L3))
                                                   (@defaultArrayEmitter
                                                     (emitters L3)))))
                                  (a!108 (not (sc_secure (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!110 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!111 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!113 ((_ is domain)
                                           (@0SomeDomain (url_host (wd_location O3)))))
                                  (a!114 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!115 (@0domain (@0SomeDomain (url_host (wd_location O3)))))
                                  (a!116 (@0domain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!117 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!118 (@1subdomain (@0SomeDomain (url_host (wd_location O3)))))
                                  (a!120 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!121 ((_ is domain)
                                           (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!122 (@0domain (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!123 (@0SomeDomain (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!124 (@1subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!125 (@0subdomain (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!129 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!131 ((_ is slash)
                                           (@0url_path_res (url_path (rq_url D4)))))
                                  (a!132 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!133 (@0anypath (@0url_path_res (url_path (rq_url D4)))))
                                  (a!134 (@0anypath (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!136 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!138 (not (sc_secure (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!140 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!141 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!143 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!144 (@0domain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!145 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!147 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!148 (@0SomeDomain (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!152 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!154 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!155 (@0anypath (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!157 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!159 (not (sc_secure (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!161 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!162 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!164 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!165 (@0domain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!166 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!168 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!169 (@0SomeDomain (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!173 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!175 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!176 (@0anypath (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!178 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!180 (not (sc_secure (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!182 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!183 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!185 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!186 (@0domain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!187 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!189 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!190 (@0SomeDomain (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!194 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!196 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!197 (@0anypath (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!199 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!201 (not (sc_secure (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!203 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!204 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!206 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!207 (@0domain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!208 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!210 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!211 (@0SomeDomain (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!215 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!217 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!218 (@0anypath (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!220 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!222 (not (sc_secure (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!224 (= (sc_same_site (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!225 (= (sc_same_site (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!227 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!228 (@0domain (sc_reg_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!229 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!231 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!232 (@0SomeDomain (sc_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!236 (= (sc_reg_domain (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!238 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!239 (@0anypath (sc_path (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!241 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@5ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!243 (not (sc_secure (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                            H4)))))
                                  (a!245 (= (sc_same_site (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!246 (= (sc_same_site (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!248 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                             H4)))))
                                  (a!249 (@0domain (sc_reg_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!250 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!252 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                         H4)))))
                                  (a!253 (@0SomeDomain (sc_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!257 (= (sc_reg_domain (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!259 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                       H4)))))
                                  (a!260 (@0anypath (sc_path (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                                H4)))))
                                  (a!262 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@6ArrayoptionSetCookie
                                                                        H4)))))
                                  (a!264 (not (sc_secure (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            H4)))))
                                  (a!266 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             H4)))
                                            SSLax))
                                  (a!267 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             H4)))
                                            SSNone))
                                  (a!269 ((_ is domain)
                                           (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             H4)))))
                                  (a!270 (@0domain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!271 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                        H4)))))
                                  (a!273 ((_ is SomeDomain)
                                           (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                         H4)))))
                                  (a!274 (@0SomeDomain (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                     H4)))))
                                  (a!278 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                              H4)))
                                            (@0SomeDomain (url_host (rq_url D4)))))
                                  (a!280 ((_ is slash)
                                           (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       H4)))))
                                  (a!281 (@0anypath (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                H4)))))
                                  (a!283 (Build_CookieMapping
                                           (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       H4)))
                                           (sc_value (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        H4)))))
                                  (a!288 (= (rq_hd_cookie (rq_headers D4))
                                            (Build_ArrayoptionCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping
                                              NoneCookieMapping)))
                                  (a!290 (ite (= Z3 4)
                                              (@4ArrayoptionBlob I4)
                                              (ite (= Z3 5)
                                                   (@5ArrayoptionBlob I4)
                                                   (ite (= Z3 6)
                                                        (@6ArrayoptionBlob I4)
                                                        (@defaultArrayoptionBlob
                                                          I4)))))
                                  (a!293 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            0))
                                  (a!294 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!295 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            1))
                                  (a!296 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!297 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            2))
                                  (a!298 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!299 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            3))
                                  (a!300 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!301 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            4))
                                  (a!302 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!303 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            5))
                                  (a!304 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!305 (= (@0DOMIndex (@1DOMPath (@0EmitterScript M3)))
                                            6))
                                  (a!306 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!307 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document O3)))))
                                  (a!313 (not ((_ is DOMTopLevel)
                                                (@1DOMPath (@0EmitterScript M3)))))
                                  (a!315 (and (c_earlyhtml5_form_methods
                                                (config L3))
                                              ((_ is MethodDelete)
                                                (form_method (@1EmitterForm M3)))))
                                  (a!318 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            0))
                                  (a!319 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            1))
                                  (a!320 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            2))
                                  (a!321 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            3))
                                  (a!322 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            4))
                                  (a!323 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            5))
                                  (a!324 (= (@0DOMIndex (@1DOMPath (@0EmitterForm M3)))
                                            6))
                                  (a!327 (not ((_ is DOMTopLevel)
                                                (@1DOMPath (@0EmitterForm M3)))))
                                  (a!329 ((_ is ProtocolHTTPS)
                                           (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                   M3)))))
                                  (a!330 ((_ is ProtocolHTTP)
                                           (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                   M3)))))
                                  (a!331 (TupleOrigin (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                              M3)))
                                                      (url_host (rq_url (@1EmitterCORSPreflight
                                                                          M3)))
                                                      (url_port (rq_url (@1EmitterCORSPreflight
                                                                          M3)))))
                                  (a!332 ((_ is ProtocolData)
                                           (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                   M3)))))
                                  (a!333 ((_ is url_path_data)
                                           (url_path (rq_url (@1EmitterCORSPreflight
                                                               M3)))))
                                  (a!334 (@0url_path_data (url_path (rq_url (@1EmitterCORSPreflight
                                                                              M3)))))
                                  (a!335 ((_ is url_path_blob)
                                           (url_path (rq_url (@1EmitterCORSPreflight
                                                               M3)))))
                                  (a!336 (@0url_path_blob (url_path (rq_url (@1EmitterCORSPreflight
                                                                              M3)))))
                                  (a!339 (or ((_ is ProtocolHTTPS)
                                               (url_protocol (wd_location O3)))
                                             ((_ is ProtocolHTTP)
                                               (url_protocol (wd_location O3)))))
                                  (a!340 (SomeOrigin (TupleOrigin (url_protocol (wd_location O3))
                                                                  (url_host (wd_location O3))
                                                                  (url_port (wd_location O3)))))
                                  (a!341 (OpaqueOrigin (@0url_path_data (url_path (wd_location O3)))))
                                  (a!343 (SomeOrigin (@0url_path_blob (url_path (wd_location O3)))))
                                  (a!348 (not (= (rq_method (@1EmitterCORSPreflight
                                                              M3))
                                                 MethodGet)))
                                  (a!349 (not (= (rq_method (@1EmitterCORSPreflight
                                                              M3))
                                                 MethodPost)))
                                  (a!351 (and (= (rq_hd_origin (rq_headers D4))
                                                 NoneOrigin)
                                              (= (rq_method D4) MethodGet)
                                              (= (rq_hd_referer (rq_headers D4))
                                                 NoneURL)
                                              (= (rq_body D4) NoneInt)))
                                  (a!352 (SomeOrigin (TupleOrigin (url_protocol (rq_url D4))
                                                                  (url_host (rq_url D4))
                                                                  (url_port (rq_url D4)))))
                                  (a!353 (OpaqueOrigin (@0url_path_data (url_path (rq_url D4)))))
                                  (a!355 (SomeOrigin (@0url_path_blob (url_path (rq_url D4)))))
                                  (a!359 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 6)
                                              (@6ArrayEmitter (emitters L3))
                                              (@defaultArrayEmitter
                                                (emitters L3))))
                                  (a!366 (rp_hd_access_control_allow_origin
                                           (rp_headers (@0SomeResponse (ft_response C4)))))
                                  (a!372 ((_ is SomeReferrerPolicy)
                                           (rp_hd_referrer_policy
                                             (dc_headers (wd_document O3)))))
                                  (a!373 (@0SomeReferrerPolicy
                                           (rp_hd_referrer_policy
                                             (dc_headers (wd_document O3)))))
                                  (a!379 (not ((_ is MethodDelete)
                                                (form_method (@1EmitterForm M3)))))
                                  (a!386 (and (or (= M3 EmitterClient)
                                                  (= M3 EmitterWorker)
                                                  (= M3 (EmitterForm V3 W3))
                                                  (= M3 (EmitterScript T3 U3)))
                                              (not (c_redirect_preflight_requests
                                                     (config L3)))))
                                  (a!388 (= (rq_hd_origin (rq_headers D4))
                                            (rq_hd_origin (rq_headers (ft_request C4)))))
                                  (a!389 ((_ is ProtocolHTTPS)
                                           (url_protocol (rq_url (ft_request C4)))))
                                  (a!390 ((_ is ProtocolHTTP)
                                           (url_protocol (rq_url (ft_request C4)))))
                                  (a!391 (TupleOrigin (url_protocol (rq_url (ft_request C4)))
                                                      (url_host (rq_url (ft_request C4)))
                                                      (url_port (rq_url (ft_request C4)))))
                                  (a!392 ((_ is ProtocolData)
                                           (url_protocol (rq_url (ft_request C4)))))
                                  (a!393 ((_ is url_path_data)
                                           (url_path (rq_url (ft_request C4)))))
                                  (a!394 (@0url_path_data (url_path (rq_url (ft_request C4)))))
                                  (a!395 ((_ is url_path_blob)
                                           (url_path (rq_url (ft_request C4)))))
                                  (a!396 (@0url_path_blob (url_path (rq_url (ft_request C4)))))
                                  (a!408 (consEvent (EvRequest M3
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
                                  (a!19 (ite (= G1 4)
                                             a!15
                                             (ite (= G1 5)
                                                  a!16
                                                  (ite (= G1 6) a!17 a!18))))
                                  (a!24 (ite (= (frame_window J1) 3)
                                             (@3ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 4)
                                                  (@4ArrayWindow (windows O1))
                                                  a!23)))
                                  (a!37 (ite (= D2 4)
                                             a!33
                                             (ite (= D2 5)
                                                  a!34
                                                  (ite (= D2 6) a!35 a!36))))
                                  (a!50 (ite (= D 4)
                                             a!46
                                             (ite (= D 5)
                                                  a!47
                                                  (ite (= D 6) a!48 a!49))))
                                  (a!55 (ite (= (frame_window G) 3)
                                             (@3ArrayWindow (windows L))
                                             (ite (= (frame_window G) 4)
                                                  (@4ArrayWindow (windows L))
                                                  a!54)))
                                  (a!68 (ite (= A1 4)
                                             a!64
                                             (ite (= A1 5)
                                                  a!65
                                                  (ite (= A1 6) a!66 a!67))))
                                  (a!81 (ite (= L2 4)
                                             a!77
                                             (ite (= L2 5)
                                                  a!78
                                                  (ite (= L2 6) a!79 a!80))))
                                  (a!86 (ite (= (frame_window O2) 3)
                                             (@3ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 4)
                                                  (@4ArrayWindow (windows T2))
                                                  a!85)))
                                  (a!99 (ite (= I3 4)
                                             a!95
                                             (ite (= I3 5)
                                                  a!96
                                                  (ite (= I3 6) a!97 a!98))))
                                  (a!104 (ite (= H2 3)
                                              (@3ArrayEmitter (emitters L3))
                                              (ite (= H2 4)
                                                   (@4ArrayEmitter (emitters L3))
                                                   a!103)))
                                  (a!109 (or a!108
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!112 (ite ((_ is EmitterClient) M3)
                                              (or a!110 a!111)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!111
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!111))))
                                  (a!126 (ite ((_ is domain) a!123)
                                              (= a!124 (@0domain a!123))
                                              (and (= a!125 (@0subdomain a!123))
                                                   (= a!124 (@1subdomain a!123)))))
                                  (a!130 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!129))
                                  (a!139 (or a!138
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!142 (ite ((_ is EmitterClient) M3)
                                              (or a!140 a!141)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!141
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!141))))
                                  (a!149 (ite ((_ is domain) a!148)
                                              (= a!124 (@0domain a!148))
                                              (and (= a!125 (@0subdomain a!148))
                                                   (= a!124 (@1subdomain a!148)))))
                                  (a!153 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!152))
                                  (a!160 (or a!159
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!163 (ite ((_ is EmitterClient) M3)
                                              (or a!161 a!162)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!162
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!162))))
                                  (a!170 (ite ((_ is domain) a!169)
                                              (= a!124 (@0domain a!169))
                                              (and (= a!125 (@0subdomain a!169))
                                                   (= a!124 (@1subdomain a!169)))))
                                  (a!174 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!173))
                                  (a!181 (or a!180
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!184 (ite ((_ is EmitterClient) M3)
                                              (or a!182 a!183)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!183
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!183))))
                                  (a!191 (ite ((_ is domain) a!190)
                                              (= a!124 (@0domain a!190))
                                              (and (= a!125 (@0subdomain a!190))
                                                   (= a!124 (@1subdomain a!190)))))
                                  (a!195 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!194))
                                  (a!202 (or a!201
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!205 (ite ((_ is EmitterClient) M3)
                                              (or a!203 a!204)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!204
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!204))))
                                  (a!212 (ite ((_ is domain) a!211)
                                              (= a!124 (@0domain a!211))
                                              (and (= a!125 (@0subdomain a!211))
                                                   (= a!124 (@1subdomain a!211)))))
                                  (a!216 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!215))
                                  (a!223 (or a!222
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!226 (ite ((_ is EmitterClient) M3)
                                              (or a!224 a!225)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!225
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!225))))
                                  (a!233 (ite ((_ is domain) a!232)
                                              (= a!124 (@0domain a!232))
                                              (and (= a!125 (@0subdomain a!232))
                                                   (= a!124 (@1subdomain a!232)))))
                                  (a!237 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!236))
                                  (a!244 (or a!243
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!247 (ite ((_ is EmitterClient) M3)
                                              (or a!245 a!246)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!246
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!246))))
                                  (a!254 (ite ((_ is domain) a!253)
                                              (= a!124 (@0domain a!253))
                                              (and (= a!125 (@0subdomain a!253))
                                                   (= a!124 (@1subdomain a!253)))))
                                  (a!258 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!257))
                                  (a!265 (or a!264
                                             (= (url_protocol (rq_url D4))
                                                ProtocolHTTPS)))
                                  (a!268 (ite ((_ is EmitterClient) M3)
                                              (or a!266 a!267)
                                              (ite (or ((_ is EmitterForm) M3)
                                                       ((_ is EmitterScript) M3))
                                                   a!267
                                                   (and ((_ is EmitterWorker)
                                                          M3)
                                                        a!267))))
                                  (a!275 (ite ((_ is domain) a!274)
                                              (= a!124 (@0domain a!274))
                                              (and (= a!125 (@0subdomain a!274))
                                                   (= a!124 (@1subdomain a!274)))))
                                  (a!279 (and ((_ is SomeDomain)
                                                (url_host (rq_url D4)))
                                              a!278))
                                  (a!289 (and (= M3 EmitterClient)
                                              (= (url_protocol (rq_url D4))
                                                 ProtocolData)
                                              a!288))
                                  (a!291 (ite (= Z3 1)
                                              (@1ArrayoptionBlob I4)
                                              (ite (= Z3 2)
                                                   (@2ArrayoptionBlob I4)
                                                   (ite (= Z3 3)
                                                        (@3ArrayoptionBlob I4)
                                                        a!290))))
                                  (a!308 (ite a!299
                                              a!300
                                              (ite a!301
                                                   a!302
                                                   (ite a!303
                                                        a!304
                                                        (ite a!305 a!306 a!307)))))
                                  (a!316 (ite ((_ is MethodPut)
                                                (form_method (@1EmitterForm M3)))
                                              (c_earlyhtml5_form_methods
                                                (config L3))
                                              a!315))
                                  (a!325 (ite a!321
                                              a!300
                                              (ite a!322
                                                   a!302
                                                   (ite a!323
                                                        a!304
                                                        (ite a!324 a!306 a!307)))))
                                  (a!337 (ite a!332
                                              (ite a!333
                                                   (SomeOrigin (OpaqueOrigin a!334))
                                                   NoneOrigin)
                                              (ite a!333
                                                   NoneOrigin
                                                   (ite a!335
                                                        (SomeOrigin a!336)
                                                        NoneOrigin))))
                                  (a!342 (ite ((_ is url_path_data)
                                                (url_path (wd_location O3)))
                                              (SomeOrigin a!341)
                                              NoneOrigin))
                                  (a!344 (ite ((_ is url_path_blob)
                                                (url_path (wd_location O3)))
                                              a!343
                                              NoneOrigin))
                                  (a!354 (ite ((_ is url_path_data)
                                                (url_path (rq_url D4)))
                                              (SomeOrigin a!353)
                                              NoneOrigin))
                                  (a!356 (ite ((_ is url_path_blob)
                                                (url_path (rq_url D4)))
                                              a!355
                                              NoneOrigin))
                                  (a!360 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 5)
                                              (@5ArrayEmitter (emitters L3))
                                              a!359))
                                  (a!367 (= (@0SomeOrigin a!366)
                                            (@0SomeOrigin (rq_hd_origin (rq_headers D4)))))
                                  (a!397 (ite a!392
                                              (ite a!393
                                                   (SomeOrigin (OpaqueOrigin a!394))
                                                   NoneOrigin)
                                              (ite a!393
                                                   NoneOrigin
                                                   (ite a!395
                                                        (SomeOrigin a!396)
                                                        NoneOrigin)))))
                            (let ((a!10 (ite ((_ is ProtocolData)
                                               (url_protocol (rq_url D4)))
                                             a!8
                                             a!9))
                                  (a!20 (ite (= G1 1)
                                             a!12
                                             (ite (= G1 2)
                                                  a!13
                                                  (ite (= G1 3) a!14 a!19))))
                                  (a!25 (ite (= (frame_window J1) 1)
                                             (@1ArrayWindow (windows O1))
                                             (ite (= (frame_window J1) 2)
                                                  (@2ArrayWindow (windows O1))
                                                  a!24)))
                                  (a!38 (ite (= D2 1)
                                             a!30
                                             (ite (= D2 2)
                                                  a!31
                                                  (ite (= D2 3) a!32 a!37))))
                                  (a!51 (ite (= D 1)
                                             a!43
                                             (ite (= D 2)
                                                  a!44
                                                  (ite (= D 3) a!45 a!50))))
                                  (a!56 (ite (= (frame_window G) 1)
                                             (@1ArrayWindow (windows L))
                                             (ite (= (frame_window G) 2)
                                                  (@2ArrayWindow (windows L))
                                                  a!55)))
                                  (a!69 (ite (= A1 1)
                                             a!61
                                             (ite (= A1 2)
                                                  a!62
                                                  (ite (= A1 3) a!63 a!68))))
                                  (a!82 (ite (= L2 1)
                                             a!74
                                             (ite (= L2 2)
                                                  a!75
                                                  (ite (= L2 3) a!76 a!81))))
                                  (a!87 (ite (= (frame_window O2) 1)
                                             (@1ArrayWindow (windows T2))
                                             (ite (= (frame_window O2) 2)
                                                  (@2ArrayWindow (windows T2))
                                                  a!86)))
                                  (a!100 (ite (= I3 1)
                                              a!92
                                              (ite (= I3 2)
                                                   a!93
                                                   (ite (= I3 3) a!94 a!99))))
                                  (a!105 (ite (= H2 1)
                                              (@1ArrayEmitter (emitters L3))
                                              (ite (= H2 2)
                                                   (@2ArrayEmitter (emitters L3))
                                                   a!104)))
                                  (a!119 (or a!112
                                             (ite a!113
                                                  (ite a!114
                                                       (= a!115 a!116)
                                                       (= a!115 a!117))
                                                  (ite a!114
                                                       (= a!118 a!116)
                                                       (= a!118 a!117)))))
                                  (a!127 (ite a!121
                                              (and (= a!122 (@0domain a!123))
                                                   ((_ is domain) a!123))
                                              a!126))
                                  (a!146 (or a!142
                                             (ite a!113
                                                  (ite a!143
                                                       (= a!115 a!144)
                                                       (= a!115 a!145))
                                                  (ite a!143
                                                       (= a!118 a!144)
                                                       (= a!118 a!145)))))
                                  (a!150 (ite a!121
                                              (and (= a!122 (@0domain a!148))
                                                   ((_ is domain) a!148))
                                              a!149))
                                  (a!167 (or a!163
                                             (ite a!113
                                                  (ite a!164
                                                       (= a!115 a!165)
                                                       (= a!115 a!166))
                                                  (ite a!164
                                                       (= a!118 a!165)
                                                       (= a!118 a!166)))))
                                  (a!171 (ite a!121
                                              (and (= a!122 (@0domain a!169))
                                                   ((_ is domain) a!169))
                                              a!170))
                                  (a!188 (or a!184
                                             (ite a!113
                                                  (ite a!185
                                                       (= a!115 a!186)
                                                       (= a!115 a!187))
                                                  (ite a!185
                                                       (= a!118 a!186)
                                                       (= a!118 a!187)))))
                                  (a!192 (ite a!121
                                              (and (= a!122 (@0domain a!190))
                                                   ((_ is domain) a!190))
                                              a!191))
                                  (a!209 (or a!205
                                             (ite a!113
                                                  (ite a!206
                                                       (= a!115 a!207)
                                                       (= a!115 a!208))
                                                  (ite a!206
                                                       (= a!118 a!207)
                                                       (= a!118 a!208)))))
                                  (a!213 (ite a!121
                                              (and (= a!122 (@0domain a!211))
                                                   ((_ is domain) a!211))
                                              a!212))
                                  (a!230 (or a!226
                                             (ite a!113
                                                  (ite a!227
                                                       (= a!115 a!228)
                                                       (= a!115 a!229))
                                                  (ite a!227
                                                       (= a!118 a!228)
                                                       (= a!118 a!229)))))
                                  (a!234 (ite a!121
                                              (and (= a!122 (@0domain a!232))
                                                   ((_ is domain) a!232))
                                              a!233))
                                  (a!251 (or a!247
                                             (ite a!113
                                                  (ite a!248
                                                       (= a!115 a!249)
                                                       (= a!115 a!250))
                                                  (ite a!248
                                                       (= a!118 a!249)
                                                       (= a!118 a!250)))))
                                  (a!255 (ite a!121
                                              (and (= a!122 (@0domain a!253))
                                                   ((_ is domain) a!253))
                                              a!254))
                                  (a!272 (or a!268
                                             (ite a!113
                                                  (ite a!269
                                                       (= a!115 a!270)
                                                       (= a!115 a!271))
                                                  (ite a!269
                                                       (= a!118 a!270)
                                                       (= a!118 a!271)))))
                                  (a!276 (ite a!121
                                              (and (= a!122 (@0domain a!274))
                                                   ((_ is domain) a!274))
                                              a!275))
                                  (a!292 (and (= M3 EmitterClient)
                                              (= (blob_origin A4) B4)
                                              (= (rq_url D4) (blob_url A4))
                                              (= (url_protocol (rq_url D4))
                                                 ProtocolBlob)
                                              a!288
                                              (= (url_path (rq_url D4))
                                                 (url_path_blob B4 Z3))
                                              (= (ite (= Z3 0)
                                                      (@0ArrayoptionBlob I4)
                                                      a!291)
                                                 (SomeBlob A4))))
                                  (a!309 (ite a!293
                                              a!294
                                              (ite a!295
                                                   a!296
                                                   (ite a!297 a!298 a!308))))
                                  (a!317 (or ((_ is MethodPost)
                                               (form_method (@1EmitterForm M3)))
                                             ((_ is MethodGet)
                                               (form_method (@1EmitterForm M3)))
                                             a!316))
                                  (a!326 (ite a!318
                                              a!294
                                              (ite a!319
                                                   a!296
                                                   (ite a!320 a!298 a!325))))
                                  (a!338 (not (= (ite (or a!329 a!330)
                                                      (SomeOrigin a!331)
                                                      a!337)
                                                 NoneOrigin)))
                                  (a!345 (ite ((_ is url_path_data)
                                                (url_path (wd_location O3)))
                                              NoneOrigin
                                              a!344))
                                  (a!357 (ite ((_ is url_path_data)
                                                (url_path (rq_url D4)))
                                              NoneOrigin
                                              a!356))
                                  (a!361 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 4)
                                              (@4ArrayEmitter (emitters L3))
                                              a!360)))
                            (let ((a!21 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= G1 0)
                                                                 a!11
                                                                 a!20))))
                                  (a!22 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= G1 0)
                                                                 a!11
                                                                 a!20))))
                                  (a!26 (= (ite (= (frame_window J1) 0)
                                                (@0ArrayWindow (windows O1))
                                                a!25)
                                           M1))
                                  (a!39 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= D2 0)
                                                                 a!29
                                                                 a!38))))
                                  (a!40 (@0DOMElementForm (@0SomeDOMElement (ite (= D2
                                                                                    0)
                                                                                 a!29
                                                                                 a!38))))
                                  (a!52 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= D 0)
                                                                 a!42
                                                                 a!51))))
                                  (a!53 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= D 0)
                                                                 a!42
                                                                 a!51))))
                                  (a!57 (= (ite (= (frame_window G) 0)
                                                (@0ArrayWindow (windows L))
                                                a!56)
                                           J))
                                  (a!70 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= A1 0)
                                                                 a!60
                                                                 a!69))))
                                  (a!71 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= A1 0)
                                                                 a!60
                                                                 a!69))))
                                  (a!83 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= L2 0)
                                                                 a!73
                                                                 a!82))))
                                  (a!84 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= L2 0)
                                                                 a!73
                                                                 a!82))))
                                  (a!88 (= (ite (= (frame_window O2) 0)
                                                (@0ArrayWindow (windows T2))
                                                a!87)
                                           R2))
                                  (a!101 (@1DOMElementResource
                                           (@0SomeDOMElement (ite (= I3 0)
                                                                  a!91
                                                                  a!100))))
                                  (a!102 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= I3 0)
                                                                  a!91
                                                                  a!100))))
                                  (a!106 (= (ite (= H2 0)
                                                 (@0ArrayEmitter (emitters L3))
                                                 a!105)
                                            (EmitterScript J2 I2)))
                                  (a!128 (and a!127
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!151 (and a!150
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!172 (and a!171
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!193 (and a!192
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!214 (and a!213
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!235 (and a!234
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!256 (and a!255
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!277 (and a!276
                                              ((_ is SomeDomain)
                                                (url_host (rq_url D4)))))
                                  (a!310 (not ((_ is ContentElementImage)
                                                (@1DOMElementResource
                                                  (@0SomeDOMElement a!309)))))
                                  (a!311 (not ((_ is ContentElementHTML)
                                                (@1DOMElementResource
                                                  (@0SomeDOMElement a!309)))))
                                  (a!312 (= (@0ContentElementScript
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!309)))
                                            (@1EmitterScript M3)))
                                  (a!328 (and a!317
                                              ((_ is DOMElementForm)
                                                (@0SomeDOMElement a!326))
                                              ((_ is SomeDOMElement) a!326)
                                              (= (@0DOMElementForm (@0SomeDOMElement a!326))
                                                 (@1EmitterForm M3))
                                              a!327))
                                  (a!346 (ite ((_ is ProtocolData)
                                                (url_protocol (wd_location O3)))
                                              a!342
                                              a!345))
                                  (a!358 (ite ((_ is ProtocolData)
                                                (url_protocol (rq_url D4)))
                                              a!354
                                              a!357))
                                  (a!362 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 3)
                                              (@3ArrayEmitter (emitters L3))
                                              a!361)))
                            (let ((a!27 (and (= (@0ContentElementFrame a!21) J1)
                                             (= (@1ContentElementFrame a!21) I1)
                                             (not ((_ is ContentElementScript)
                                                    a!21))
                                             (not ((_ is ContentElementImage)
                                                    a!21))
                                             (not ((_ is ContentElementHTML)
                                                    a!21))
                                             (not a!22)
                                             ((_ is SomeDOMElement)
                                               (ite (= G1 0) a!11 a!20))
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
                                  (a!58 (and (= (@0ContentElementFrame a!52) G)
                                             (= (@1ContentElementFrame a!52) F)
                                             (not ((_ is ContentElementScript)
                                                    a!52))
                                             (not ((_ is ContentElementImage)
                                                    a!52))
                                             (not ((_ is ContentElementHTML)
                                                    a!52))
                                             (not a!53)
                                             ((_ is SomeDOMElement)
                                               (ite (= D 0) a!42 a!51))
                                             (= R E)
                                             (= P Q)
                                             (= J Q)
                                             (= B1 K)
                                             (= K P)
                                             a!57
                                             (= C (DOMPath (consInt D H) I))
                                             (= Y C)
                                             (= N (DOMPath H I))
                                             (= N (DOMPath nilInt O))
                                             (= S L)
                                             (= L M)))
                                  (a!89 (and (= (@0ContentElementFrame a!83) O2)
                                             (= (@1ContentElementFrame a!83) N2)
                                             (not ((_ is ContentElementScript)
                                                    a!83))
                                             (not ((_ is ContentElementImage)
                                                    a!83))
                                             (not ((_ is ContentElementHTML)
                                                    a!83))
                                             (not a!84)
                                             ((_ is SomeDOMElement)
                                               (ite (= L2 0) a!73 a!82))
                                             (= J3 S2)
                                             (= Z2 M2)
                                             (= X2 Y2)
                                             (= S2 X2)
                                             (= R2 Y2)
                                             a!88
                                             (= K2 (DOMPath (consInt L2 P2) Q2))
                                             (= V2 (DOMPath P2 Q2))
                                             (= V2 (DOMPath nilInt W2))
                                             (= G3 K2)
                                             (= A3 T2)
                                             (= T2 U2)))
                                  (a!135 (and a!109
                                              a!119
                                              (ite a!120 a!128 a!130)
                                              (ite a!131
                                                   a!132
                                                   (or a!132 (= a!133 a!134)))
                                              a!3
                                              a!4))
                                  (a!156 (and a!139
                                              a!146
                                              (ite a!147 a!151 a!153)
                                              (ite a!131
                                                   a!154
                                                   (or a!154 (= a!133 a!155)))
                                              a!3
                                              a!4))
                                  (a!177 (and a!160
                                              a!167
                                              (ite a!168 a!172 a!174)
                                              (ite a!131
                                                   a!175
                                                   (or a!175 (= a!133 a!176)))
                                              a!3
                                              a!4))
                                  (a!198 (and a!181
                                              a!188
                                              (ite a!189 a!193 a!195)
                                              (ite a!131
                                                   a!196
                                                   (or a!196 (= a!133 a!197)))
                                              a!3
                                              a!4))
                                  (a!219 (and a!202
                                              a!209
                                              (ite a!210 a!214 a!216)
                                              (ite a!131
                                                   a!217
                                                   (or a!217 (= a!133 a!218)))
                                              a!3
                                              a!4))
                                  (a!240 (and a!223
                                              a!230
                                              (ite a!231 a!235 a!237)
                                              (ite a!131
                                                   a!238
                                                   (or a!238 (= a!133 a!239)))
                                              a!3
                                              a!4))
                                  (a!261 (and a!244
                                              a!251
                                              (ite a!252 a!256 a!258)
                                              (ite a!131
                                                   a!259
                                                   (or a!259 (= a!133 a!260)))
                                              a!3
                                              a!4))
                                  (a!282 (and a!265
                                              a!272
                                              (ite a!273 a!277 a!279)
                                              (ite a!131
                                                   a!280
                                                   (or a!280 (= a!133 a!281)))
                                              a!3
                                              a!4))
                                  (a!314 (and ((_ is ContentElementScript)
                                                (@1DOMElementResource
                                                  (@0SomeDOMElement a!309)))
                                              a!310
                                              a!311
                                              (not ((_ is DOMElementForm)
                                                     (@0SomeDOMElement a!309)))
                                              ((_ is SomeDOMElement) a!309)
                                              a!312
                                              a!313))
                                  (a!347 (not (= (ite (or a!329 a!330)
                                                      (SomeOrigin a!331)
                                                      a!337)
                                                 (ite a!339 a!340 a!346))))
                                  (a!363 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 2)
                                              (@2ArrayEmitter (emitters L3))
                                              a!362))
                                  (a!370 (ite ((_ is TupleOrigin)
                                                (@0SomeOrigin (ite a!339
                                                                   a!340
                                                                   a!346)))
                                              (ite a!339 a!340 a!346)
                                              NoneOrigin))
                                  (a!374 (Build_URL (@0TupleOrigin (@0SomeOrigin (ite a!339
                                                                                      a!340
                                                                                      a!346)))
                                                    (@1TupleOrigin (@0SomeOrigin (ite a!339
                                                                                      a!340
                                                                                      a!346)))
                                                    (@2TupleOrigin (@0SomeOrigin (ite a!339
                                                                                      a!340
                                                                                      a!346)))
                                                    (url_path_res slash)))
                                  (a!378 (and (c_earlyhtml5_form_methods
                                                (config L3))
                                              (not (= (ite a!2 a!352 a!358)
                                                      NoneOrigin))
                                              (= (ite a!2 a!352 a!358)
                                                 (ite a!339 a!340 a!346))))
                                  (a!398 (= (ite a!2 a!352 a!358)
                                            (ite (or a!389 a!390)
                                                 (SomeOrigin a!391)
                                                 a!397))))
                            (let ((a!28 (or (and (= E2 Z1)
                                                 (= Z1 A2)
                                                 (= U1 A2)
                                                 (= B2 X1)
                                                 (= X1 (DOMPath nilInt Y1))
                                                 (= V1 W1))
                                            a!27))
                                  (a!59 (or (and (= R X)
                                                 (= B1 W)
                                                 (= W X)
                                                 (= Y U)
                                                 (= U (DOMPath nilInt V))
                                                 (= S T))
                                            a!58))
                                  (a!90 (or (and (= J3 E3)
                                                 (= Z2 F3)
                                                 (= E3 F3)
                                                 (= G3 C3)
                                                 (= C3 (DOMPath nilInt D3))
                                                 (= A3 B3))
                                            a!89))
                                  (a!137 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!135
                                                   (SomeCookieMapping a!136)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!158 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!156
                                                   (SomeCookieMapping a!157)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!179 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!177
                                                   (SomeCookieMapping a!178)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!200 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!198
                                                   (SomeCookieMapping a!199)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!221 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!219
                                                   (SomeCookieMapping a!220)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!242 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!240
                                                   (SomeCookieMapping a!241)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!263 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!261
                                                   (SomeCookieMapping a!262)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!284 (ite ((_ is SomeDomain)
                                                (url_host (wd_location O3)))
                                              (ite a!282
                                                   (SomeCookieMapping a!283)
                                                   NoneCookieMapping)
                                              NoneCookieMapping))
                                  (a!350 (ite ((_ is EmitterScript) M3)
                                              a!314
                                              (ite ((_ is EmitterForm) M3)
                                                   a!328
                                                   (or ((_ is EmitterWorker) M3)
                                                       (and a!338
                                                            a!347
                                                            a!348
                                                            a!349)))))
                                  (a!364 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 1)
                                              (@1ArrayEmitter (emitters L3))
                                              a!363))
                                  (a!371 (= (rq_hd_origin (rq_headers D4))
                                            (ite ((_ is SomeOrigin)
                                                   (ite a!339 a!340 a!346))
                                                 a!370
                                                 (ite a!339 a!340 a!346))))
                                  (a!375 (ite ((_ is TupleOrigin)
                                                (@0SomeOrigin (ite a!339
                                                                   a!340
                                                                   a!346)))
                                              (SomeURL a!374)
                                              NoneURL))
                                  (a!380 (ite ((_ is MethodPut)
                                                (form_method (@1EmitterForm M3)))
                                              a!378
                                              (or a!378 a!379)))
                                  (a!399 (and (= (rq_hd_origin (rq_headers D4))
                                                 NoneOrigin)
                                              (not a!398))))
                            (let ((a!41 (and a!28
                                             a!39
                                             ((_ is SomeDOMElement)
                                               (ite (= D2 0) a!29 a!38))
                                             (= O3 E2)
                                             (= N3 U1)
                                             (= B2 (DOMPath C2 (DOMIndex D2)))
                                             (= E1 B2)
                                             (= L3 V1)
                                             (= D1 F2)
                                             (= a!40 F2)
                                             (= M3 (EmitterForm E1 D1))))
                                  (a!72 (and a!59
                                             ((_ is ContentElementScript) a!70)
                                             (not ((_ is ContentElementImage)
                                                    a!70))
                                             (not ((_ is ContentElementHTML)
                                                    a!70))
                                             (not a!71)
                                             ((_ is SomeDOMElement)
                                               (ite (= A1 0) a!60 a!69))
                                             (= O3 B1)
                                             (= N3 R)
                                             (= B Y)
                                             (= Y (DOMPath Z (DOMIndex A1)))
                                             (= L3 S)
                                             (= A C1)
                                             (= (@0ContentElementScript a!70)
                                                C1)
                                             (= M3 (EmitterScript B A))))
                                  (a!107 (and a!90
                                              ((_ is ContentElementScript)
                                                a!101)
                                              (not ((_ is ContentElementImage)
                                                     a!101))
                                              (not ((_ is ContentElementHTML)
                                                     a!101))
                                              (not a!102)
                                              ((_ is SomeDOMElement)
                                                (ite (= I3 0) a!91 a!100))
                                              (= O3 J3)
                                              (= N3 Z2)
                                              (= G3 (DOMPath H3 (DOMIndex I3)))
                                              (= J2 G3)
                                              (= L3 A3)
                                              (= I2 K3)
                                              (= (@0ContentElementScript a!101)
                                                 K3)
                                              (= M3
                                                 (EmitterCORSPreflight H2 G2))
                                              a!106))
                                  (a!285 (Build_ArrayoptionCookieMapping
                                           (ite ((_ is SomeSetCookie)
                                                  (@0ArrayoptionSetCookie H4))
                                                a!137
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@1ArrayoptionSetCookie H4))
                                                a!158
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@2ArrayoptionSetCookie H4))
                                                a!179
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@3ArrayoptionSetCookie H4))
                                                a!200
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@4ArrayoptionSetCookie H4))
                                                a!221
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@5ArrayoptionSetCookie H4))
                                                a!242
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@6ArrayoptionSetCookie H4))
                                                a!263
                                                NoneCookieMapping)
                                           (ite ((_ is SomeSetCookie)
                                                  (@defaultArrayoptionSetCookie
                                                    H4))
                                                a!284
                                                NoneCookieMapping)))
                                  (a!365 (ite (= (@0EmitterCORSPreflight
                                                   (ft_emitter C4))
                                                 0)
                                              (@0ArrayEmitter (emitters L3))
                                              a!364))
                                  (a!376 (ite ((_ is ReferrerPolicyNoReferrer)
                                                a!373)
                                              NoneURL
                                              (ite ((_ is SomeOrigin)
                                                     (ite a!339 a!340 a!346))
                                                   a!375
                                                   NoneURL)))
                                  (a!381 (or ((_ is MethodPost)
                                               (form_method (@1EmitterForm M3)))
                                             ((_ is MethodGet)
                                               (form_method (@1EmitterForm M3)))
                                             a!380))
                                  (a!400 (and (or (and a!388 a!398) a!399)
                                              (not (c_origin_header_on_cross_origin_redirect
                                                     (config L3))))))
                            (let ((a!286 (and (= (url_protocol (rq_url D4))
                                                 ProtocolHTTP)
                                              (= (rq_hd_cookie (rq_headers D4))
                                                 a!285)))
                                  (a!287 (and (= (url_protocol (rq_url D4))
                                                 ProtocolHTTPS)
                                              (= (rq_hd_cookie (rq_headers D4))
                                                 a!285)))
                                  (a!368 (and (= M3 a!365)
                                              (not ((_ is EmitterWorker)
                                                     (ft_emitter C4)))
                                              (not ((_ is EmitterForm)
                                                     (ft_emitter C4)))
                                              (not ((_ is EmitterScript)
                                                     (ft_emitter C4)))
                                              (not ((_ is EmitterClient)
                                                     (ft_emitter C4)))
                                              ((_ is SomeOrigin) a!366)
                                              ((_ is SomeOrigin)
                                                (rq_hd_origin (rq_headers D4)))
                                              (= D4
                                                 (@1EmitterCORSPreflight
                                                   (ft_emitter C4)))
                                              a!367
                                              ((_ is SomeResponse)
                                                (ft_response C4))))
                                  (a!382 (and a!381
                                              a!371
                                              (= (rq_method D4)
                                                 (form_method (@1EmitterForm M3)))
                                              (= (rq_hd_referer (rq_headers D4))
                                                 (ite a!372 a!376 NoneURL))
                                              (= (rq_url D4)
                                                 (form_action (@1EmitterForm M3)))))
                                  (a!384 (and a!371
                                              (not (= (ite a!2 a!352 a!358)
                                                      NoneOrigin))
                                              (not (= (ite a!2 a!352 a!358)
                                                      (ite a!339 a!340 a!346)))
                                              (= (rq_method D4) MethodOptions)
                                              (= (rq_hd_referer (rq_headers D4))
                                                 (ite a!372 a!376 NoneURL))
                                              (= (rq_body D4) NoneInt)
                                              (= (rq_url D4)
                                                 (rq_url (@1EmitterCORSPreflight
                                                           M3)))))
                                  (a!401 (or (and (c_origin_header_on_cross_origin_redirect
                                                    (config L3))
                                                  a!388)
                                             a!400)))
                            (let ((a!369 (or (= (rq_method D4) MethodGet)
                                             (= (rq_method D4) MethodPost)
                                             (= (ite a!2 a!352 a!358)
                                                (ite a!339 a!340 a!346))
                                             (= (ite a!2 a!352 a!358)
                                                NoneOrigin)
                                             a!368))
                                  (a!402 (and a!401
                                              (= (ft_emitter C4) M3)
                                              (= (rq_method D4) MethodGet)
                                              (= (rp_hd_location (rp_headers Y3))
                                                 (SomeURL S3))
                                              (= (rq_hd_referer (rq_headers D4))
                                                 NoneURL)
                                              (= (rq_body D4) NoneInt)
                                              (= (rq_url D4) S3)))
                                  (a!404 (and a!401
                                              (= (ft_emitter C4) M3)
                                              (= (rq_method D4)
                                                 (rq_method (ft_request C4)))
                                              (= (rp_hd_location (rp_headers Y3))
                                                 (SomeURL X3))
                                              (= (rq_hd_referer (rq_headers D4))
                                                 NoneURL)
                                              (= (rq_body D4)
                                                 (rq_body (ft_request C4)))
                                              (= (rq_url D4) X3))))
                            (let ((a!377 (and a!369
                                              a!371
                                              (= (rq_hd_referer (rq_headers D4))
                                                 (ite a!372 a!376 NoneURL))))
                                  (a!383 (and a!369
                                              a!371
                                              (= (rq_hd_referer (rq_headers D4))
                                                 NoneURL))))
                            (let ((a!385 (ite ((_ is EmitterScript) M3)
                                              a!377
                                              (ite ((_ is EmitterForm) M3)
                                                   a!382
                                                   (ite ((_ is EmitterWorker)
                                                          M3)
                                                        a!383
                                                        a!384)))))
                            (let ((a!387 (and (ite ((_ is EmitterClient) M3)
                                                   a!351
                                                   a!385)
                                              (= (rp_hd_location (rp_headers Y3))
                                                 NoneURL))))
                            (let ((a!403 (and (or (c_redirect_preflight_requests
                                                    (config L3))
                                                  a!386)
                                              (or a!387 a!402)
                                              (= (rp_code Y3) ResponseFound)))
                                  (a!405 (and (or (c_redirect_preflight_requests
                                                    (config L3))
                                                  a!386)
                                              (or a!387 a!404)
                                              (= (rp_code Y3)
                                                 ResponseTemporaryRedirect))))
                            (let ((a!406 (or (and (ite ((_ is EmitterClient) M3)
                                                       a!351
                                                       a!385)
                                                  (= (rp_code Y3) ResponseOk))
                                             (and (ite ((_ is EmitterClient) M3)
                                                       a!351
                                                       a!385)
                                                  (= (rp_code Y3)
                                                     ResponseNoContent))
                                             a!403
                                             a!405)))
                            (let ((a!407 (or (and a!406
                                                  (= (ft_response C4)
                                                     (SomeResponse Y3)))
                                             (and (ite ((_ is EmitterClient) M3)
                                                       a!351
                                                       a!385)
                                                  (= (ft_response C4)
                                                     NoneResponse)))))
                            (let ((a!409 (and (Reachable L3 E4 P3)
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
                                                  a!41
                                                  a!72
                                                  a!107)
                                              (or a!286 a!287 a!289 a!292)
                                              (or ((_ is EmitterClient) M3)
                                                  a!350)
                                              a!407
                                              (= R3 a!408))))
                              (=> a!409 (Reachable L3 R3 Q3))))))))))))))))))
                            :weight 0))))
      (a!124 (asserted (forall ((A State)
                                (B State)
                                (C listEvent)
                                (D NestedDOMPath)
                                (E Int)
                                (F Window)
                                (G HTML)
                                (H Frame)
                                (I listInt)
                                (J DOMSelector)
                                (K Window)
                                (L Window)
                                (M Global)
                                (N Global)
                                (O NestedDOMPath)
                                (P DOMSelector)
                                (Q Window)
                                (R Window)
                                (S Global)
                                (T NestedDOMPath)
                                (U DOMSelector)
                                (V Window)
                                (W Window)
                                (X NestedDOMPath)
                                (Y listInt)
                                (Z Int)
                                (A1 Window)
                                (B1 Script)
                                (C1 NestedDOMPath)
                                (D1 Int)
                                (E1 Window)
                                (F1 HTML)
                                (G1 Frame)
                                (H1 listInt)
                                (I1 DOMSelector)
                                (J1 Window)
                                (K1 Window)
                                (L1 Global)
                                (M1 Global)
                                (N1 NestedDOMPath)
                                (O1 DOMSelector)
                                (P1 Window)
                                (Q1 Window)
                                (R1 NestedDOMPath)
                                (S1 Window)
                                (T1 Window)
                                (U1 Global)
                                (V1 Global)
                                (W1 NestedDOMPath)
                                (X1 DOMSelector)
                                (Y1 Window)
                                (Z1 Window)
                                (A2 listInt)
                                (B2 Int)
                                (C2 HTML)
                                (D2 NestedDOMPath)
                                (E2 HTML)
                                (F2 listInt)
                                (G2 DOMSelector)
                                (H2 HTMLElement)
                                (I2 Window)
                                (J2 Global)
                                (K2 NestedDOMPath)
                                (L2 Window)
                                (M2 Window)
                                (N2 Int)
                                (O2 Int)
                                (P2 HTMLElement)
                                (Q2 Window)
                                (R2 Global)
                                (S2 Window)
                                (T2 Int)
                                (U2 Int)
                                (V2 Window)
                                (W2 Frame)
                                (X2 Int)
                                (Y2 Window)
                                (Z2 Window)
                                (A3 Global)
                                (B3 NestedDOMPath)
                                (C3 Window)
                                (D3 Window)
                                (E3 Int)
                                (F3 Int)
                                (G3 HTMLElement)
                                (H3 Window)
                                (I3 NestedDOMPath)
                                (J3 listInt)
                                (K3 DOMSelector)
                                (L3 optionInt)
                                (M3 Int)
                                (N3 Global)
                                (O3 NestedDOMPath)
                                (P3 Window)
                                (Q3 Int)
                                (R3 optionInt)
                                (S3 Window)
                                (T3 Global)
                                (U3 Window)
                                (V3 Window)
                                (W3 Int)
                                (X3 Int)
                                (Y3 Window)
                                (Z3 Frame)
                                (A4 Int)
                                (B4 HTML)
                                (C4 Window)
                                (D4 Window)
                                (E4 Int)
                                (F4 Int)
                                (G4 Global)
                                (H4 NestedDOMPath)
                                (I4 Window)
                                (J4 Int)
                                (K4 optionInt)
                                (L4 Window)
                                (M4 Int)
                                (N4 Blob)
                                (O4 Origin)
                                (P4 Frame)
                                (Q4 URL)
                                (R4 listEvent)
                                (S4 Int)
                                (T4 FetchEngine)
                                (U4 ServiceWorker)
                                (V4 Window)
                                (W4 ArrayoptionSetCookie)
                                (X4 ArrayoptionBlob)
                                (Y4 ArrayoptionStorageItem))
                         (! (let ((a!1 (Build_State (+ 1 S4) T4 U4 V4 W4 X4 Y4))
                                  (a!2 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!3 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!4 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!5 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!6 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!7 (@5ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!8 (@6ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!9 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                  (a!13 (ite (= E4 5)
                                             (@5ArrayWindow (windows U1))
                                             (ite (= E4 6)
                                                  (@6ArrayWindow (windows U1))
                                                  (@defaultArrayWindow
                                                    (windows U1)))))
                                  (a!17 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!18 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!19 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!20 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!21 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!22 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!23 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!24 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document T1)))))
                                  (a!30 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location A1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location A1)))))
                                  (a!31 (SomeOrigin (TupleOrigin (url_protocol (wd_location A1))
                                                                 (url_host (wd_location A1))
                                                                 (url_port (wd_location A1)))))
                                  (a!32 (OpaqueOrigin (@0url_path_data (url_path (wd_location A1)))))
                                  (a!34 (SomeOrigin (@0url_path_blob (url_path (wd_location A1)))))
                                  (a!38 (ite (= M4 4)
                                             (@4ArrayoptionBlob X4)
                                             (ite (= M4 5)
                                                  (@5ArrayoptionBlob X4)
                                                  (ite (= M4 6)
                                                       (@6ArrayoptionBlob X4)
                                                       (@defaultArrayoptionBlob
                                                         X4)))))
                                  (a!41 (and ((_ is SomeDomain)
                                               (wd_document_domain C3))
                                             (= (url_protocol (wd_location H3))
                                                (url_protocol (wd_location C3)))
                                             (= (@0SomeDomain (wd_document_domain
                                                                H3))
                                                (@0SomeDomain (wd_document_domain
                                                                C3)))))
                                  (a!42 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location H3)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location H3)))))
                                  (a!43 (SomeOrigin (TupleOrigin (url_protocol (wd_location H3))
                                                                 (url_host (wd_location H3))
                                                                 (url_port (wd_location H3)))))
                                  (a!44 (OpaqueOrigin (@0url_path_data (url_path (wd_location H3)))))
                                  (a!46 (SomeOrigin (@0url_path_blob (url_path (wd_location H3)))))
                                  (a!50 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location C3)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location C3)))))
                                  (a!51 (SomeOrigin (TupleOrigin (url_protocol (wd_location C3))
                                                                 (url_host (wd_location C3))
                                                                 (url_port (wd_location C3)))))
                                  (a!52 (OpaqueOrigin (@0url_path_data (url_path (wd_location C3)))))
                                  (a!54 (SomeOrigin (@0url_path_blob (url_path (wd_location C3)))))
                                  (a!59 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!60 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!61 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!62 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!63 (@5ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!64 (@6ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!65 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!66 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document H3)))))
                                  (a!72 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm G3)
                                                                                    (@1HTMLForm G3)))))
                                  (a!74 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!75 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!76 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!77 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!78 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!79 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!80 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!81 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document H3)))))
                                  (a!88 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!89 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!90 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!91 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!92 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!93 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!94 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!95 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Z2)))))
                                  (a!99 (and ((_ is SomeDomain)
                                               (wd_document_domain L2))
                                             (= (url_protocol (wd_location Q2))
                                                (url_protocol (wd_location L2)))
                                             (= (@0SomeDomain (wd_document_domain
                                                                Q2))
                                                (@0SomeDomain (wd_document_domain
                                                                L2)))))
                                  (a!100 (or ((_ is ProtocolHTTPS)
                                               (url_protocol (wd_location Q2)))
                                             ((_ is ProtocolHTTP)
                                               (url_protocol (wd_location Q2)))))
                                  (a!101 (SomeOrigin (TupleOrigin (url_protocol (wd_location Q2))
                                                                  (url_host (wd_location Q2))
                                                                  (url_port (wd_location Q2)))))
                                  (a!102 (OpaqueOrigin (@0url_path_data (url_path (wd_location Q2)))))
                                  (a!104 (SomeOrigin (@0url_path_blob (url_path (wd_location Q2)))))
                                  (a!108 (or ((_ is ProtocolHTTPS)
                                               (url_protocol (wd_location L2)))
                                             ((_ is ProtocolHTTP)
                                               (url_protocol (wd_location L2)))))
                                  (a!109 (SomeOrigin (TupleOrigin (url_protocol (wd_location L2))
                                                                  (url_host (wd_location L2))
                                                                  (url_port (wd_location L2)))))
                                  (a!110 (OpaqueOrigin (@0url_path_data (url_path (wd_location L2)))))
                                  (a!112 (SomeOrigin (@0url_path_blob (url_path (wd_location L2)))))
                                  (a!118 (DOMElementResource
                                           (wd_location V2)
                                           (ContentElementFrame
                                             (Build_Frame (frame_src W2) X2)
                                             (dc_html (wd_document Y2)))))
                                  (a!125 (@1ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!126 (@2ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!127 (@3ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!128 (@4ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!129 (@5ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!130 (@6ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!131 (@defaultArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!132 (@0ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q2)))))
                                  (a!138 (SomeDOMElement (DOMElementForm (Build_Form (@0HTMLForm P2)
                                                                                     (@1HTMLForm P2)))))
                                  (a!140 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!141 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!142 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!143 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!144 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!145 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!146 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!147 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q2)))))
                                  (a!153 (ite (= X2 5)
                                              (@5ArrayWindow (windows R2))
                                              (ite (= X2 6)
                                                   (@6ArrayWindow (windows R2))
                                                   (@defaultArrayWindow
                                                     (windows R2)))))
                                  (a!157 (ite (= (frame_window W2) 5)
                                              (@5ArrayWindow (windows R2))
                                              (ite (= (frame_window W2) 6)
                                                   (@6ArrayWindow (windows R2))
                                                   (@defaultArrayWindow
                                                     (windows R2)))))
                                  (a!162 (@1ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!163 (@2ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!164 (@3ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!165 (@4ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!166 (@5ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!167 (@6ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!168 (@defaultArrayoptionInt
                                           (in_body (dc_init (wd_document L4)))))
                                  (a!169 (@0ArrayoptionInt (in_body (dc_init (wd_document L4)))))
                                  (a!176 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!177 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!178 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!179 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!180 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!181 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!182 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!183 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document C4)))))
                                  (a!188 (DOMElementResource
                                           (wd_location Y3)
                                           (ContentElementFrame
                                             (Build_Frame (frame_src Z3) A4)
                                             B4)))
                                  (a!195 (@1ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!196 (@2ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!197 (@3ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!198 (@4ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!199 (@5ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!200 (@6ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!201 (@defaultArrayoptionInt
                                           (in_body (dc_init (wd_document S3)))))
                                  (a!202 (@0ArrayoptionInt (in_body (dc_init (wd_document S3)))))
                                  (a!208 (ite (= A4 5)
                                              (@5ArrayWindow (windows T3))
                                              (ite (= A4 6)
                                                   (@6ArrayWindow (windows T3))
                                                   (@defaultArrayWindow
                                                     (windows T3)))))
                                  (a!212 (ite (= (frame_window Z3) 5)
                                              (@5ArrayWindow (windows T3))
                                              (ite (= (frame_window Z3) 6)
                                                   (@6ArrayWindow (windows T3))
                                                   (@defaultArrayWindow
                                                     (windows T3)))))
                                  (a!217 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!218 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!219 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!220 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!221 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!222 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!223 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!224 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document F)))))
                                  (a!229 (ite (= (frame_window H) 5)
                                              (@5ArrayWindow (windows M))
                                              (ite (= (frame_window H) 6)
                                                   (@6ArrayWindow (windows M))
                                                   (@defaultArrayWindow
                                                     (windows M)))))
                                  (a!235 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!236 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!237 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!238 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!239 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!240 (@5ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!241 (@6ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!242 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document E1)))))
                                  (a!247 (ite (= (frame_window G1) 5)
                                              (@5ArrayWindow (windows L1))
                                              (ite (= (frame_window G1) 6)
                                                   (@6ArrayWindow (windows L1))
                                                   (@defaultArrayWindow
                                                     (windows L1))))))
                            (let ((a!10 (ite (= Z 4)
                                             a!6
                                             (ite (= Z 5)
                                                  a!7
                                                  (ite (= Z 6) a!8 a!9))))
                                  (a!14 (ite (= E4 3)
                                             (@3ArrayWindow (windows U1))
                                             (ite (= E4 4)
                                                  (@4ArrayWindow (windows U1))
                                                  a!13)))
                                  (a!25 (ite (= B2 4)
                                             a!21
                                             (ite (= B2 5)
                                                  a!22
                                                  (ite (= B2 6) a!23 a!24))))
                                  (a!33 (ite ((_ is url_path_data)
                                               (url_path (wd_location A1)))
                                             (SomeOrigin a!32)
                                             NoneOrigin))
                                  (a!35 (ite ((_ is url_path_blob)
                                               (url_path (wd_location A1)))
                                             a!34
                                             NoneOrigin))
                                  (a!39 (ite (= M4 1)
                                             (@1ArrayoptionBlob X4)
                                             (ite (= M4 2)
                                                  (@2ArrayoptionBlob X4)
                                                  (ite (= M4 3)
                                                       (@3ArrayoptionBlob X4)
                                                       a!38))))
                                  (a!45 (ite ((_ is url_path_data)
                                               (url_path (wd_location H3)))
                                             (SomeOrigin a!44)
                                             NoneOrigin))
                                  (a!47 (ite ((_ is url_path_blob)
                                               (url_path (wd_location H3)))
                                             a!46
                                             NoneOrigin))
                                  (a!53 (ite ((_ is url_path_data)
                                               (url_path (wd_location C3)))
                                             (SomeOrigin a!52)
                                             NoneOrigin))
                                  (a!55 (ite ((_ is url_path_blob)
                                               (url_path (wd_location C3)))
                                             a!54
                                             NoneOrigin))
                                  (a!67 (ite (= F3 6)
                                             (Build_ArrayoptionHTMLElement
                                               a!66
                                               a!59
                                               a!60
                                               a!61
                                               a!62
                                               a!63
                                               (SomeHTMLElement G3)
                                               a!65)
                                             (html_body (dc_html (wd_document H3)))))
                                  (a!73 (ite (or ((_ is HTMLImage) G3)
                                                 ((_ is HTMLScript) G3))
                                             NoneDOMElement
                                             (ite ((_ is HTMLForm) G3)
                                                  a!72
                                                  NoneDOMElement)))
                                  (a!96 (ite (= U2 4)
                                             a!92
                                             (ite (= U2 5)
                                                  a!93
                                                  (ite (= U2 6) a!94 a!95))))
                                  (a!103 (ite ((_ is url_path_data)
                                                (url_path (wd_location Q2)))
                                              (SomeOrigin a!102)
                                              NoneOrigin))
                                  (a!105 (ite ((_ is url_path_blob)
                                                (url_path (wd_location Q2)))
                                              a!104
                                              NoneOrigin))
                                  (a!111 (ite ((_ is url_path_data)
                                                (url_path (wd_location L2)))
                                              (SomeOrigin a!110)
                                              NoneOrigin))
                                  (a!113 (ite ((_ is url_path_blob)
                                                (url_path (wd_location L2)))
                                              a!112
                                              NoneOrigin))
                                  (a!119 (ite (= U2 6)
                                              (Build_ArrayoptionDOMElement
                                                a!88
                                                a!89
                                                a!90
                                                a!91
                                                a!92
                                                a!93
                                                (SomeDOMElement a!118)
                                                a!95)
                                              (dm_body (dc_dom (wd_document Z2)))))
                                  (a!133 (ite (= O2 6)
                                              (Build_ArrayoptionHTMLElement
                                                a!132
                                                a!125
                                                a!126
                                                a!127
                                                a!128
                                                a!129
                                                (SomeHTMLElement P2)
                                                a!131)
                                              (html_body (dc_html (wd_document Q2)))))
                                  (a!139 (ite (or ((_ is HTMLImage) P2)
                                                  ((_ is HTMLScript) P2))
                                              NoneDOMElement
                                              (ite ((_ is HTMLForm) P2)
                                                   a!138
                                                   NoneDOMElement)))
                                  (a!154 (ite (= X2 3)
                                              (@3ArrayWindow (windows R2))
                                              (ite (= X2 4)
                                                   (@4ArrayWindow (windows R2))
                                                   a!153)))
                                  (a!158 (ite (= (frame_window W2) 3)
                                              (@3ArrayWindow (windows R2))
                                              (ite (= (frame_window W2) 4)
                                                   (@4ArrayWindow (windows R2))
                                                   a!157)))
                                  (a!170 (ite (= J4 6)
                                              (Build_ArrayoptionInt
                                                a!169
                                                a!162
                                                a!163
                                                a!164
                                                a!165
                                                a!166
                                                K4
                                                a!168)
                                              (in_body (dc_init (wd_document L4)))))
                                  (a!184 (ite (= X3 4)
                                              a!180
                                              (ite (= X3 5)
                                                   a!181
                                                   (ite (= X3 6) a!182 a!183))))
                                  (a!189 (ite (= X3 6)
                                              (Build_ArrayoptionDOMElement
                                                a!176
                                                a!177
                                                a!178
                                                a!179
                                                a!180
                                                a!181
                                                (SomeDOMElement a!188)
                                                a!183)
                                              (dm_body (dc_dom (wd_document C4)))))
                                  (a!203 (ite (= Q3 6)
                                              (Build_ArrayoptionInt
                                                a!202
                                                a!195
                                                a!196
                                                a!197
                                                a!198
                                                a!199
                                                R3
                                                a!201)
                                              (in_body (dc_init (wd_document S3)))))
                                  (a!209 (ite (= A4 3)
                                              (@3ArrayWindow (windows T3))
                                              (ite (= A4 4)
                                                   (@4ArrayWindow (windows T3))
                                                   a!208)))
                                  (a!213 (ite (= (frame_window Z3) 3)
                                              (@3ArrayWindow (windows T3))
                                              (ite (= (frame_window Z3) 4)
                                                   (@4ArrayWindow (windows T3))
                                                   a!212)))
                                  (a!225 (ite (= E 4)
                                              a!221
                                              (ite (= E 5)
                                                   a!222
                                                   (ite (= E 6) a!223 a!224))))
                                  (a!230 (ite (= (frame_window H) 3)
                                              (@3ArrayWindow (windows M))
                                              (ite (= (frame_window H) 4)
                                                   (@4ArrayWindow (windows M))
                                                   a!229)))
                                  (a!243 (ite (= D1 4)
                                              a!239
                                              (ite (= D1 5)
                                                   a!240
                                                   (ite (= D1 6) a!241 a!242))))
                                  (a!248 (ite (= (frame_window G1) 3)
                                              (@3ArrayWindow (windows L1))
                                              (ite (= (frame_window G1) 4)
                                                   (@4ArrayWindow (windows L1))
                                                   a!247))))
                            (let ((a!11 (ite (= Z 1)
                                             a!3
                                             (ite (= Z 2)
                                                  a!4
                                                  (ite (= Z 3) a!5 a!10))))
                                  (a!15 (ite (= E4 1)
                                             (@1ArrayWindow (windows U1))
                                             (ite (= E4 2)
                                                  (@2ArrayWindow (windows U1))
                                                  a!14)))
                                  (a!26 (ite (= B2 1)
                                             a!18
                                             (ite (= B2 2)
                                                  a!19
                                                  (ite (= B2 3) a!20 a!25))))
                                  (a!36 (ite ((_ is url_path_data)
                                               (url_path (wd_location A1)))
                                             NoneOrigin
                                             a!35))
                                  (a!48 (ite ((_ is url_path_data)
                                               (url_path (wd_location H3)))
                                             NoneOrigin
                                             a!47))
                                  (a!56 (ite ((_ is url_path_data)
                                               (url_path (wd_location C3)))
                                             NoneOrigin
                                             a!55))
                                  (a!68 (ite (= F3 4)
                                             (Build_ArrayoptionHTMLElement
                                               a!66
                                               a!59
                                               a!60
                                               a!61
                                               (SomeHTMLElement G3)
                                               a!63
                                               a!64
                                               a!65)
                                             (ite (= F3 5)
                                                  (Build_ArrayoptionHTMLElement
                                                    a!66
                                                    a!59
                                                    a!60
                                                    a!61
                                                    a!62
                                                    (SomeHTMLElement G3)
                                                    a!64
                                                    a!65)
                                                  a!67)))
                                  (a!82 (ite (= F3 6)
                                             (Build_ArrayoptionDOMElement
                                               a!81
                                               a!74
                                               a!75
                                               a!76
                                               a!77
                                               a!78
                                               a!73
                                               a!80)
                                             (dm_body (dc_dom (wd_document H3)))))
                                  (a!97 (ite (= U2 1)
                                             a!89
                                             (ite (= U2 2)
                                                  a!90
                                                  (ite (= U2 3) a!91 a!96))))
                                  (a!106 (ite ((_ is url_path_data)
                                                (url_path (wd_location Q2)))
                                              NoneOrigin
                                              a!105))
                                  (a!114 (ite ((_ is url_path_data)
                                                (url_path (wd_location L2)))
                                              NoneOrigin
                                              a!113))
                                  (a!120 (ite (= U2 4)
                                              (Build_ArrayoptionDOMElement
                                                a!88
                                                a!89
                                                a!90
                                                a!91
                                                (SomeDOMElement a!118)
                                                a!93
                                                a!94
                                                a!95)
                                              (ite (= U2 5)
                                                   (Build_ArrayoptionDOMElement
                                                     a!88
                                                     a!89
                                                     a!90
                                                     a!91
                                                     a!92
                                                     (SomeDOMElement a!118)
                                                     a!94
                                                     a!95)
                                                   a!119)))
                                  (a!134 (ite (= O2 4)
                                              (Build_ArrayoptionHTMLElement
                                                a!132
                                                a!125
                                                a!126
                                                a!127
                                                (SomeHTMLElement P2)
                                                a!129
                                                a!130
                                                a!131)
                                              (ite (= O2 5)
                                                   (Build_ArrayoptionHTMLElement
                                                     a!132
                                                     a!125
                                                     a!126
                                                     a!127
                                                     a!128
                                                     (SomeHTMLElement P2)
                                                     a!130
                                                     a!131)
                                                   a!133)))
                                  (a!148 (ite (= O2 6)
                                              (Build_ArrayoptionDOMElement
                                                a!147
                                                a!140
                                                a!141
                                                a!142
                                                a!143
                                                a!144
                                                a!139
                                                a!146)
                                              (dm_body (dc_dom (wd_document Q2)))))
                                  (a!155 (ite (= X2 1)
                                              (@1ArrayWindow (windows R2))
                                              (ite (= X2 2)
                                                   (@2ArrayWindow (windows R2))
                                                   a!154)))
                                  (a!159 (ite (= (frame_window W2) 1)
                                              (@1ArrayWindow (windows R2))
                                              (ite (= (frame_window W2) 2)
                                                   (@2ArrayWindow (windows R2))
                                                   a!158)))
                                  (a!171 (ite (= J4 3)
                                              (Build_ArrayoptionInt
                                                a!169
                                                a!162
                                                a!163
                                                K4
                                                a!165
                                                a!166
                                                a!167
                                                a!168)
                                              (ite (= J4 4)
                                                   (Build_ArrayoptionInt
                                                     a!169
                                                     a!162
                                                     a!163
                                                     a!164
                                                     K4
                                                     a!166
                                                     a!167
                                                     a!168)
                                                   (ite (= J4 5)
                                                        (Build_ArrayoptionInt
                                                          a!169
                                                          a!162
                                                          a!163
                                                          a!164
                                                          a!165
                                                          K4
                                                          a!167
                                                          a!168)
                                                        a!170))))
                                  (a!185 (ite (= X3 1)
                                              a!177
                                              (ite (= X3 2)
                                                   a!178
                                                   (ite (= X3 3) a!179 a!184))))
                                  (a!190 (ite (= X3 4)
                                              (Build_ArrayoptionDOMElement
                                                a!176
                                                a!177
                                                a!178
                                                a!179
                                                (SomeDOMElement a!188)
                                                a!181
                                                a!182
                                                a!183)
                                              (ite (= X3 5)
                                                   (Build_ArrayoptionDOMElement
                                                     a!176
                                                     a!177
                                                     a!178
                                                     a!179
                                                     a!180
                                                     (SomeDOMElement a!188)
                                                     a!182
                                                     a!183)
                                                   a!189)))
                                  (a!204 (ite (= Q3 3)
                                              (Build_ArrayoptionInt
                                                a!202
                                                a!195
                                                a!196
                                                R3
                                                a!198
                                                a!199
                                                a!200
                                                a!201)
                                              (ite (= Q3 4)
                                                   (Build_ArrayoptionInt
                                                     a!202
                                                     a!195
                                                     a!196
                                                     a!197
                                                     R3
                                                     a!199
                                                     a!200
                                                     a!201)
                                                   (ite (= Q3 5)
                                                        (Build_ArrayoptionInt
                                                          a!202
                                                          a!195
                                                          a!196
                                                          a!197
                                                          a!198
                                                          R3
                                                          a!200
                                                          a!201)
                                                        a!203))))
                                  (a!210 (ite (= A4 1)
                                              (@1ArrayWindow (windows T3))
                                              (ite (= A4 2)
                                                   (@2ArrayWindow (windows T3))
                                                   a!209)))
                                  (a!214 (ite (= (frame_window Z3) 1)
                                              (@1ArrayWindow (windows T3))
                                              (ite (= (frame_window Z3) 2)
                                                   (@2ArrayWindow (windows T3))
                                                   a!213)))
                                  (a!226 (ite (= E 1)
                                              a!218
                                              (ite (= E 2)
                                                   a!219
                                                   (ite (= E 3) a!220 a!225))))
                                  (a!231 (ite (= (frame_window H) 1)
                                              (@1ArrayWindow (windows M))
                                              (ite (= (frame_window H) 2)
                                                   (@2ArrayWindow (windows M))
                                                   a!230)))
                                  (a!244 (ite (= D1 1)
                                              a!236
                                              (ite (= D1 2)
                                                   a!237
                                                   (ite (= D1 3) a!238 a!243))))
                                  (a!249 (ite (= (frame_window G1) 1)
                                              (@1ArrayWindow (windows L1))
                                              (ite (= (frame_window G1) 2)
                                                   (@2ArrayWindow (windows L1))
                                                   a!248))))
                            (let ((a!12 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= Z 0)
                                                                 a!2
                                                                 a!11))))
                                  (a!16 (= (ite (= E4 0)
                                                (@0ArrayWindow (windows U1))
                                                a!15)
                                           A1))
                                  (a!27 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= Z 0)
                                                                 a!2
                                                                 a!11))))
                                  (a!28 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= B2 0)
                                                                 a!17
                                                                 a!26))))
                                  (a!29 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= B2 0)
                                                                 a!17
                                                                 a!26))))
                                  (a!37 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location A1)))
                                             a!33
                                             a!36))
                                  (a!49 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location H3)))
                                             a!45
                                             a!48))
                                  (a!57 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location C3)))
                                             a!53
                                             a!56))
                                  (a!69 (ite (= F3 2)
                                             (Build_ArrayoptionHTMLElement
                                               a!66
                                               a!59
                                               (SomeHTMLElement G3)
                                               a!61
                                               a!62
                                               a!63
                                               a!64
                                               a!65)
                                             (ite (= F3 3)
                                                  (Build_ArrayoptionHTMLElement
                                                    a!66
                                                    a!59
                                                    a!60
                                                    (SomeHTMLElement G3)
                                                    a!62
                                                    a!63
                                                    a!64
                                                    a!65)
                                                  a!68)))
                                  (a!83 (ite (= F3 3)
                                             (Build_ArrayoptionDOMElement
                                               a!81
                                               a!74
                                               a!75
                                               a!73
                                               a!77
                                               a!78
                                               a!79
                                               a!80)
                                             (ite (= F3 4)
                                                  (Build_ArrayoptionDOMElement
                                                    a!81
                                                    a!74
                                                    a!75
                                                    a!76
                                                    a!73
                                                    a!78
                                                    a!79
                                                    a!80)
                                                  (ite (= F3 5)
                                                       (Build_ArrayoptionDOMElement
                                                         a!81
                                                         a!74
                                                         a!75
                                                         a!76
                                                         a!77
                                                         a!73
                                                         a!79
                                                         a!80)
                                                       a!82))))
                                  (a!98 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= U2 0)
                                                                 a!88
                                                                 a!97))))
                                  (a!107 (ite ((_ is ProtocolData)
                                                (url_protocol (wd_location Q2)))
                                              a!103
                                              a!106))
                                  (a!115 (ite ((_ is ProtocolData)
                                                (url_protocol (wd_location L2)))
                                              a!111
                                              a!114))
                                  (a!117 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= U2 0)
                                                                  a!88
                                                                  a!97))))
                                  (a!121 (ite (= U2 2)
                                              (Build_ArrayoptionDOMElement
                                                a!88
                                                a!89
                                                (SomeDOMElement a!118)
                                                a!91
                                                a!92
                                                a!93
                                                a!94
                                                a!95)
                                              (ite (= U2 3)
                                                   (Build_ArrayoptionDOMElement
                                                     a!88
                                                     a!89
                                                     a!90
                                                     (SomeDOMElement a!118)
                                                     a!92
                                                     a!93
                                                     a!94
                                                     a!95)
                                                   a!120)))
                                  (a!135 (ite (= O2 2)
                                              (Build_ArrayoptionHTMLElement
                                                a!132
                                                a!125
                                                (SomeHTMLElement P2)
                                                a!127
                                                a!128
                                                a!129
                                                a!130
                                                a!131)
                                              (ite (= O2 3)
                                                   (Build_ArrayoptionHTMLElement
                                                     a!132
                                                     a!125
                                                     a!126
                                                     (SomeHTMLElement P2)
                                                     a!128
                                                     a!129
                                                     a!130
                                                     a!131)
                                                   a!134)))
                                  (a!149 (ite (= O2 3)
                                              (Build_ArrayoptionDOMElement
                                                a!147
                                                a!140
                                                a!141
                                                a!139
                                                a!143
                                                a!144
                                                a!145
                                                a!146)
                                              (ite (= O2 4)
                                                   (Build_ArrayoptionDOMElement
                                                     a!147
                                                     a!140
                                                     a!141
                                                     a!142
                                                     a!139
                                                     a!144
                                                     a!145
                                                     a!146)
                                                   (ite (= O2 5)
                                                        (Build_ArrayoptionDOMElement
                                                          a!147
                                                          a!140
                                                          a!141
                                                          a!142
                                                          a!143
                                                          a!139
                                                          a!145
                                                          a!146)
                                                        a!148))))
                                  (a!156 (= (ite (= X2 0)
                                                 (@0ArrayWindow (windows R2))
                                                 a!155)
                                            Y2))
                                  (a!160 (= (ite (= (frame_window W2) 0)
                                                 (@0ArrayWindow (windows R2))
                                                 a!159)
                                            V2))
                                  (a!172 (ite (= J4 0)
                                              (Build_ArrayoptionInt
                                                K4
                                                a!162
                                                a!163
                                                a!164
                                                a!165
                                                a!166
                                                a!167
                                                a!168)
                                              (ite (= J4 1)
                                                   (Build_ArrayoptionInt
                                                     a!169
                                                     K4
                                                     a!163
                                                     a!164
                                                     a!165
                                                     a!166
                                                     a!167
                                                     a!168)
                                                   (ite (= J4 2)
                                                        (Build_ArrayoptionInt
                                                          a!169
                                                          a!162
                                                          K4
                                                          a!164
                                                          a!165
                                                          a!166
                                                          a!167
                                                          a!168)
                                                        a!171))))
                                  (a!186 (@1DOMElementResource
                                           (@0SomeDOMElement (ite (= X3 0)
                                                                  a!176
                                                                  a!185))))
                                  (a!187 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= X3 0)
                                                                  a!176
                                                                  a!185))))
                                  (a!191 (ite (= X3 2)
                                              (Build_ArrayoptionDOMElement
                                                a!176
                                                a!177
                                                (SomeDOMElement a!188)
                                                a!179
                                                a!180
                                                a!181
                                                a!182
                                                a!183)
                                              (ite (= X3 3)
                                                   (Build_ArrayoptionDOMElement
                                                     a!176
                                                     a!177
                                                     a!178
                                                     (SomeDOMElement a!188)
                                                     a!180
                                                     a!181
                                                     a!182
                                                     a!183)
                                                   a!190)))
                                  (a!205 (ite (= Q3 0)
                                              (Build_ArrayoptionInt
                                                R3
                                                a!195
                                                a!196
                                                a!197
                                                a!198
                                                a!199
                                                a!200
                                                a!201)
                                              (ite (= Q3 1)
                                                   (Build_ArrayoptionInt
                                                     a!202
                                                     R3
                                                     a!196
                                                     a!197
                                                     a!198
                                                     a!199
                                                     a!200
                                                     a!201)
                                                   (ite (= Q3 2)
                                                        (Build_ArrayoptionInt
                                                          a!202
                                                          a!195
                                                          R3
                                                          a!197
                                                          a!198
                                                          a!199
                                                          a!200
                                                          a!201)
                                                        a!204))))
                                  (a!211 (= (ite (= A4 0)
                                                 (@0ArrayWindow (windows T3))
                                                 a!210)
                                            U3))
                                  (a!215 (= (ite (= (frame_window Z3) 0)
                                                 (@0ArrayWindow (windows T3))
                                                 a!214)
                                            Y3))
                                  (a!227 (@1DOMElementResource
                                           (@0SomeDOMElement (ite (= E 0)
                                                                  a!217
                                                                  a!226))))
                                  (a!228 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= E 0)
                                                                  a!217
                                                                  a!226))))
                                  (a!232 (= (ite (= (frame_window H) 0)
                                                 (@0ArrayWindow (windows M))
                                                 a!231)
                                            K))
                                  (a!245 (@1DOMElementResource
                                           (@0SomeDOMElement (ite (= D1 0)
                                                                  a!235
                                                                  a!244))))
                                  (a!246 ((_ is DOMElementForm)
                                           (@0SomeDOMElement (ite (= D1 0)
                                                                  a!235
                                                                  a!244))))
                                  (a!250 (= (ite (= (frame_window G1) 0)
                                                 (@0ArrayWindow (windows L1))
                                                 a!249)
                                            J1)))
                            (let ((a!40 (and (= (SomeOrigin O4)
                                                (ite a!30 a!31 a!37))
                                             (= (blob_origin N4) O4)
                                             (= Q4 (blob_url N4))
                                             (= (url_protocol Q4) ProtocolBlob)
                                             (= (url_path Q4)
                                                (url_path_blob O4 M4))
                                             (= (ite (= M4 0)
                                                     (@0ArrayoptionBlob X4)
                                                     a!39)
                                                (SomeBlob N4))))
                                  (a!58 (and (not (= (ite a!42 a!43 a!49)
                                                     NoneOrigin))
                                             (= (ite a!42 a!43 a!49)
                                                (ite a!50 a!51 a!57))
                                             (not ((_ is SomeDomain)
                                                    (wd_document_domain C3)))))
                                  (a!70 (ite (= F3 0)
                                             (Build_ArrayoptionHTMLElement
                                               (SomeHTMLElement G3)
                                               a!59
                                               a!60
                                               a!61
                                               a!62
                                               a!63
                                               a!64
                                               a!65)
                                             (ite (= F3 1)
                                                  (Build_ArrayoptionHTMLElement
                                                    a!66
                                                    (SomeHTMLElement G3)
                                                    a!60
                                                    a!61
                                                    a!62
                                                    a!63
                                                    a!64
                                                    a!65)
                                                  a!69)))
                                  (a!84 (ite (= F3 0)
                                             (Build_ArrayoptionDOMElement
                                               a!73
                                               a!74
                                               a!75
                                               a!76
                                               a!77
                                               a!78
                                               a!79
                                               a!80)
                                             (ite (= F3 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!81
                                                    a!73
                                                    a!75
                                                    a!76
                                                    a!77
                                                    a!78
                                                    a!79
                                                    a!80)
                                                  (ite (= F3 2)
                                                       (Build_ArrayoptionDOMElement
                                                         a!81
                                                         a!74
                                                         a!73
                                                         a!76
                                                         a!77
                                                         a!78
                                                         a!79
                                                         a!80)
                                                       a!83))))
                                  (a!116 (and (not (= (ite a!100 a!101 a!107)
                                                      NoneOrigin))
                                              (= (ite a!100 a!101 a!107)
                                                 (ite a!108 a!109 a!115))
                                              (not ((_ is SomeDomain)
                                                     (wd_document_domain L2)))))
                                  (a!122 (ite (= U2 0)
                                              (Build_ArrayoptionDOMElement
                                                (SomeDOMElement a!118)
                                                a!89
                                                a!90
                                                a!91
                                                a!92
                                                a!93
                                                a!94
                                                a!95)
                                              (ite (= U2 1)
                                                   (Build_ArrayoptionDOMElement
                                                     a!88
                                                     (SomeDOMElement a!118)
                                                     a!90
                                                     a!91
                                                     a!92
                                                     a!93
                                                     a!94
                                                     a!95)
                                                   a!121)))
                                  (a!136 (ite (= O2 0)
                                              (Build_ArrayoptionHTMLElement
                                                (SomeHTMLElement P2)
                                                a!125
                                                a!126
                                                a!127
                                                a!128
                                                a!129
                                                a!130
                                                a!131)
                                              (ite (= O2 1)
                                                   (Build_ArrayoptionHTMLElement
                                                     a!132
                                                     (SomeHTMLElement P2)
                                                     a!126
                                                     a!127
                                                     a!128
                                                     a!129
                                                     a!130
                                                     a!131)
                                                   a!135)))
                                  (a!150 (ite (= O2 0)
                                              (Build_ArrayoptionDOMElement
                                                a!139
                                                a!140
                                                a!141
                                                a!142
                                                a!143
                                                a!144
                                                a!145
                                                a!146)
                                              (ite (= O2 1)
                                                   (Build_ArrayoptionDOMElement
                                                     a!147
                                                     a!139
                                                     a!141
                                                     a!142
                                                     a!143
                                                     a!144
                                                     a!145
                                                     a!146)
                                                   (ite (= O2 2)
                                                        (Build_ArrayoptionDOMElement
                                                          a!147
                                                          a!140
                                                          a!139
                                                          a!142
                                                          a!143
                                                          a!144
                                                          a!145
                                                          a!146)
                                                        a!149))))
                                  (a!173 (Build_Initiators (in_toplevel (dc_init (wd_document L4)))
                                                           a!172))
                                  (a!192 (ite (= X3 0)
                                              (Build_ArrayoptionDOMElement
                                                (SomeDOMElement a!188)
                                                a!177
                                                a!178
                                                a!179
                                                a!180
                                                a!181
                                                a!182
                                                a!183)
                                              (ite (= X3 1)
                                                   (Build_ArrayoptionDOMElement
                                                     a!176
                                                     (SomeDOMElement a!188)
                                                     a!178
                                                     a!179
                                                     a!180
                                                     a!181
                                                     a!182
                                                     a!183)
                                                   a!191)))
                                  (a!206 (Build_Initiators (in_toplevel (dc_init (wd_document S3)))
                                                           a!205))
                                  (a!233 (and (= (@0ContentElementFrame a!227)
                                                 H)
                                              (= (@1ContentElementFrame a!227)
                                                 G)
                                              (not ((_ is ContentElementScript)
                                                     a!227))
                                              (not ((_ is ContentElementImage)
                                                     a!227))
                                              (not ((_ is ContentElementHTML)
                                                     a!227))
                                              (not a!228)
                                              ((_ is SomeDOMElement)
                                                (ite (= E 0) a!217 a!226))
                                              (= S1 F)
                                              (= A1 L)
                                              (= L Q)
                                              (= Q R)
                                              (= K R)
                                              a!232
                                              (= X D)
                                              (= O (DOMPath I J))
                                              (= O (DOMPath nilInt P))
                                              (= D (DOMPath (consInt E I) J))
                                              (= M N)
                                              (= U1 M)))
                                  (a!251 (and (= (@0ContentElementFrame a!245)
                                                 G1)
                                              (= (@1ContentElementFrame a!245)
                                                 F1)
                                              (not ((_ is ContentElementScript)
                                                     a!245))
                                              (not ((_ is ContentElementImage)
                                                     a!245))
                                              (not ((_ is ContentElementHTML)
                                                     a!245))
                                              (not a!246)
                                              ((_ is SomeDOMElement)
                                                (ite (= D1 0) a!235 a!244))
                                              (= T1 K1)
                                              (= S1 E1)
                                              (= K1 P1)
                                              (= J1 Q1)
                                              (= P1 Q1)
                                              a!250
                                              (= R1 C1)
                                              (= N1 (DOMPath H1 I1))
                                              (= N1 (DOMPath nilInt O1))
                                              (= C1
                                                 (DOMPath (consInt D1 H1) I1))
                                              (= U1 L1)
                                              (= L1 M1))))
                            (let ((a!71 (Build_HTML (html_nonce (dc_html (wd_document H3)))
                                                    (html_head (dc_html (wd_document H3)))
                                                    a!70))
                                  (a!85 (Build_DOM (dm_nonce (dc_dom (wd_document H3)))
                                                   (dm_head (dc_dom (wd_document H3)))
                                                   a!84))
                                  (a!123 (Build_DOM (dm_nonce (dc_dom (wd_document Z2)))
                                                    (dm_head (dc_dom (wd_document Z2)))
                                                    a!122))
                                  (a!137 (Build_HTML (html_nonce (dc_html (wd_document Q2)))
                                                     (html_head (dc_html (wd_document Q2)))
                                                     a!136))
                                  (a!151 (Build_DOM (dm_nonce (dc_dom (wd_document Q2)))
                                                    (dm_head (dc_dom (wd_document Q2)))
                                                    a!150))
                                  (a!174 (Build_Window (wd_nonce L4)
                                                       (wd_parent L4)
                                                       (wd_location L4)
                                                       (wd_document_domain L4)
                                                       (Build_Document (dc_version (wd_document L4))
                                                                       (dc_nonce (wd_document L4))
                                                                       (dc_headers (wd_document L4))
                                                                       (dc_html (wd_document L4))
                                                                       (dc_dom (wd_document L4))
                                                                       a!173)))
                                  (a!193 (Build_DOM (dm_nonce (dc_dom (wd_document C4)))
                                                    (dm_head (dc_dom (wd_document C4)))
                                                    a!192))
                                  (a!207 (Build_Window (wd_nonce S3)
                                                       (wd_parent S3)
                                                       (wd_location S3)
                                                       (wd_document_domain S3)
                                                       (Build_Document (dc_version (wd_document S3))
                                                                       (dc_nonce (wd_document S3))
                                                                       (dc_headers (wd_document S3))
                                                                       (dc_html (wd_document S3))
                                                                       (dc_dom (wd_document S3))
                                                                       a!206)))
                                  (a!234 (or (and (= S1 W)
                                                  (= A1 V)
                                                  (= V W)
                                                  (= T (DOMPath nilInt U))
                                                  (= X T)
                                                  (= U1 S))
                                             a!233))
                                  (a!252 (or (and (= T1 Y1)
                                                  (= Y1 Z1)
                                                  (= S1 Z1)
                                                  (= R1 W1)
                                                  (= W1 (DOMPath nilInt X1))
                                                  (= U1 V1))
                                             a!251)))
                            (let ((a!86 (Build_Window (wd_nonce H3)
                                                      (wd_parent H3)
                                                      (wd_location H3)
                                                      (wd_document_domain H3)
                                                      (Build_Document (+ 1 E3)
                                                                      (dc_nonce (wd_document H3))
                                                                      (dc_headers (wd_document H3))
                                                                      a!71
                                                                      a!85
                                                                      (dc_init (wd_document H3)))))
                                  (a!124 (Build_Window (wd_nonce Z2)
                                                       (wd_parent Z2)
                                                       (wd_location Z2)
                                                       (wd_document_domain Z2)
                                                       (Build_Document (+ 1 T2)
                                                                       (dc_nonce (wd_document Z2))
                                                                       (dc_headers (wd_document Z2))
                                                                       (dc_html (wd_document Z2))
                                                                       a!123
                                                                       (dc_init (wd_document Z2)))))
                                  (a!152 (Build_Window (wd_nonce Q2)
                                                       (wd_parent Q2)
                                                       (wd_location Q2)
                                                       (wd_document_domain Q2)
                                                       (Build_Document (+ 1 N2)
                                                                       (dc_nonce (wd_document Q2))
                                                                       (dc_headers (wd_document Q2))
                                                                       a!137
                                                                       a!151
                                                                       (dc_init (wd_document Q2)))))
                                  (a!175 (and (= S4 F4)
                                              (= V4 I4)
                                              (= D4 L4)
                                              (= I4 a!174)
                                              (= H4
                                                 (DOMPath nilInt (DOMIndex J4)))
                                              (= R1 H4)
                                              (= U1 G4)
                                              (= K4 (SomeInt E4))))
                                  (a!194 (Build_Window (wd_nonce C4)
                                                       (wd_parent C4)
                                                       (wd_location C4)
                                                       (wd_document_domain C4)
                                                       (Build_Document (+ 1 W3)
                                                                       (dc_nonce (wd_document C4))
                                                                       (dc_headers (wd_document C4))
                                                                       (dc_html (wd_document C4))
                                                                       a!193
                                                                       (dc_init (wd_document C4))))))
                            (let ((a!87 (and (= S4 E3)
                                             (ite ((_ is SomeDomain)
                                                    (wd_document_domain H3))
                                                  a!41
                                                  a!58)
                                             (= D4 D3)
                                             (= D3 a!86)
                                             (= T1 C3)
                                             (= S1 H3)
                                             (= B3
                                                (DOMPath nilInt (DOMIndex F3)))
                                             (= R1 B3)
                                             (= U1 A3)
                                             (= G3 (HTMLFrame Q4))))
                                  (a!161 (and (= S4 T2)
                                              (= T2 N2)
                                              (= (@0ContentElementFrame a!98)
                                                 W2)
                                              (= (@1ContentElementFrame a!98)
                                                 E2)
                                              (not ((_ is ContentElementScript)
                                                     a!98))
                                              (ite ((_ is SomeDomain)
                                                     (wd_document_domain Q2))
                                                   a!99
                                                   a!116)
                                              (not ((_ is ContentElementImage)
                                                     a!98))
                                              (not ((_ is ContentElementHTML)
                                                     a!98))
                                              (not a!117)
                                              ((_ is SomeDOMElement)
                                                (ite (= U2 0) a!88 a!97))
                                              (= D4 S2)
                                              (= T1 I2)
                                              (= Y2 M2)
                                              (= S1 Z2)
                                              (= V2 Q2)
                                              (= S2 a!124)
                                              (= M2 a!152)
                                              (= I2 L2)
                                              a!156
                                              a!160
                                              (= K2 (DOMPath F2 G2))
                                              (= K2
                                                 (DOMPath nilInt (DOMIndex O2)))
                                              (= R1 D2)
                                              (= D2
                                                 (DOMPath (consInt U2 F2) G2))
                                              (= R2 J2)
                                              (= U1 R2)
                                              (= H2 P2)
                                              (= H2 (HTMLFrame Q4))))
                                  (a!216 (and (= S4 W3)
                                              (= W3 M3)
                                              (= (@0ContentElementFrame a!186)
                                                 Z3)
                                              (= (@1ContentElementFrame a!186)
                                                 B4)
                                              (not ((_ is ContentElementScript)
                                                     a!186))
                                              (not ((_ is ContentElementImage)
                                                     a!186))
                                              (not ((_ is ContentElementHTML)
                                                     a!186))
                                              (not a!187)
                                              ((_ is SomeDOMElement)
                                                (ite (= X3 0) a!176 a!185))
                                              (= V4 V3)
                                              (= D4 C4)
                                              (= Y3 S3)
                                              (= U3 P3)
                                              (= V3 a!194)
                                              (= P3 a!207)
                                              a!211
                                              a!215
                                              (= I3
                                                 (DOMPath (consInt X3 J3) K3))
                                              (= O3 (DOMPath J3 K3))
                                              (= O3
                                                 (DOMPath nilInt (DOMIndex Q3)))
                                              (= R1 I3)
                                              (= T3 N3)
                                              (= U1 T3)
                                              (= L3 R3)
                                              (= L3 (SomeInt E4)))))
                            (let ((a!253 (and (Reachable U1 R4 A)
                                              (= A
                                                 (Build_State S4
                                                              T4
                                                              U4
                                                              S1
                                                              W4
                                                              X4
                                                              Y4))
                                              (= B a!1)
                                              (= (@0ContentElementScript a!12)
                                                 B1)
                                              (= X (DOMPath Y (DOMIndex Z)))
                                              (= R1 (DOMPath A2 (DOMIndex B2)))
                                              a!16
                                              ((_ is SomeDOMElement)
                                                (ite (= Z 0) a!2 a!11))
                                              ((_ is SomeDOMElement)
                                                (ite (= B2 0) a!17 a!26))
                                              (not a!27)
                                              (not a!28)
                                              (not ((_ is ContentElementHTML)
                                                     a!12))
                                              (not ((_ is ContentElementHTML)
                                                     a!29))
                                              (not ((_ is ContentElementImage)
                                                     a!12))
                                              (not ((_ is ContentElementImage)
                                                     a!29))
                                              ((_ is ContentElementScript) a!12)
                                              (not ((_ is ContentElementScript)
                                                     a!29))
                                              (= (@1ContentElementFrame a!29)
                                                 C2)
                                              (= (@0ContentElementFrame a!29)
                                                 P4)
                                              (or (= (url_protocol Q4)
                                                     ProtocolData)
                                                  (= (url_protocol Q4)
                                                     ProtocolHTTPS)
                                                  (= (url_protocol Q4)
                                                     ProtocolHTTP)
                                                  a!40)
                                              (or a!87 a!161)
                                              (or a!175 a!216)
                                              a!234
                                              a!252
                                              (= C
                                                 (consEvent (EvScriptNavigateFrame
                                                              X
                                                              R1
                                                              P4
                                                              Q4)
                                                            R4)))))
                              (=> a!253 (Reachable U1 C B)))))))))))
                            :weight 0))))
      (a!126 (asserted (forall ((A State)
                                (B State)
                                (C listEvent)
                                (D NestedDOMPath)
                                (E Int)
                                (F Window)
                                (G HTML)
                                (H Frame)
                                (I listInt)
                                (J DOMSelector)
                                (K Window)
                                (L Window)
                                (M Global)
                                (N Global)
                                (O NestedDOMPath)
                                (P DOMSelector)
                                (Q Window)
                                (R Window)
                                (S Window)
                                (T Global)
                                (U Global)
                                (V NestedDOMPath)
                                (W DOMSelector)
                                (X Window)
                                (Y Window)
                                (Z NestedDOMPath)
                                (A1 listInt)
                                (B1 Int)
                                (C1 Window)
                                (D1 Script)
                                (E1 Origin)
                                (F1 Int)
                                (G1 Blob)
                                (H1 ArrayoptionBlob)
                                (I1 URL)
                                (J1 listEvent)
                                (K1 Int)
                                (L1 FetchEngine)
                                (M1 ServiceWorker)
                                (N1 ArrayoptionSetCookie)
                                (O1 ArrayoptionBlob)
                                (P1 ArrayoptionStorageItem))
                         (! (let ((a!1 (ite (= F1 5)
                                            (Build_ArrayoptionBlob
                                              (@0ArrayoptionBlob H1)
                                              (@1ArrayoptionBlob H1)
                                              (@2ArrayoptionBlob H1)
                                              (@3ArrayoptionBlob H1)
                                              (@4ArrayoptionBlob H1)
                                              (SomeBlob G1)
                                              (@6ArrayoptionBlob H1)
                                              (@defaultArrayoptionBlob H1))
                                            (ite (= F1 6)
                                                 (Build_ArrayoptionBlob
                                                   (@0ArrayoptionBlob H1)
                                                   (@1ArrayoptionBlob H1)
                                                   (@2ArrayoptionBlob H1)
                                                   (@3ArrayoptionBlob H1)
                                                   (@4ArrayoptionBlob H1)
                                                   (@5ArrayoptionBlob H1)
                                                   (SomeBlob G1)
                                                   (@defaultArrayoptionBlob H1))
                                                 H1)))
                                  (a!5 (ite (= F1 4)
                                            (@4ArrayoptionBlob H1)
                                            (ite (= F1 5)
                                                 (@5ArrayoptionBlob H1)
                                                 (ite (= F1 6)
                                                      (@6ArrayoptionBlob H1)
                                                      (@defaultArrayoptionBlob
                                                        H1)))))
                                  (a!7 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location C1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location C1)))))
                                  (a!8 (SomeOrigin (TupleOrigin (url_protocol (wd_location C1))
                                                                (url_host (wd_location C1))
                                                                (url_port (wd_location C1)))))
                                  (a!9 (OpaqueOrigin (@0url_path_data (url_path (wd_location C1)))))
                                  (a!11 (SomeOrigin (@0url_path_blob (url_path (wd_location C1)))))
                                  (a!15 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!16 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!17 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!18 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!19 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!20 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!21 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!22 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document C1)))))
                                  (a!27 (and (not ((_ is url_path_blob)
                                                    (url_path I1)))
                                             (not ((_ is url_path_data)
                                                    (url_path I1)))
                                             ((_ is SomeInt) (url_port I1))
                                             ((_ is SomeDomain) (url_host I1))))
                                  (a!28 (and ((_ is url_path_data)
                                               (url_path I1))
                                             (not ((_ is SomeInt) (url_port I1)))
                                             (not ((_ is SomeDomain)
                                                    (url_host I1)))))
                                  (a!29 (and ((_ is url_path_blob)
                                               (url_path I1))
                                             (not ((_ is url_path_data)
                                                    (url_path I1)))
                                             (not ((_ is SomeInt) (url_port I1)))
                                             (not ((_ is SomeDomain)
                                                    (url_host I1)))))
                                  (a!31 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!32 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!33 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!34 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!35 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!36 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!37 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!38 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document F)))))
                                  (a!43 (ite (= (frame_window H) 5)
                                             (@5ArrayWindow (windows M))
                                             (ite (= (frame_window H) 6)
                                                  (@6ArrayWindow (windows M))
                                                  (@defaultArrayWindow
                                                    (windows M)))))
                                  (a!49 (= (blob_csp G1)
                                           (rp_hd_csp (dc_headers (wd_document C1))))))
                            (let ((a!2 (ite (= F1 3)
                                            (Build_ArrayoptionBlob
                                              (@0ArrayoptionBlob H1)
                                              (@1ArrayoptionBlob H1)
                                              (@2ArrayoptionBlob H1)
                                              (SomeBlob G1)
                                              (@4ArrayoptionBlob H1)
                                              (@5ArrayoptionBlob H1)
                                              (@6ArrayoptionBlob H1)
                                              (@defaultArrayoptionBlob H1))
                                            (ite (= F1 4)
                                                 (Build_ArrayoptionBlob
                                                   (@0ArrayoptionBlob H1)
                                                   (@1ArrayoptionBlob H1)
                                                   (@2ArrayoptionBlob H1)
                                                   (@3ArrayoptionBlob H1)
                                                   (SomeBlob G1)
                                                   (@5ArrayoptionBlob H1)
                                                   (@6ArrayoptionBlob H1)
                                                   (@defaultArrayoptionBlob H1))
                                                 a!1)))
                                  (a!6 (ite (= F1 1)
                                            (@1ArrayoptionBlob H1)
                                            (ite (= F1 2)
                                                 (@2ArrayoptionBlob H1)
                                                 (ite (= F1 3)
                                                      (@3ArrayoptionBlob H1)
                                                      a!5))))
                                  (a!10 (ite ((_ is url_path_data)
                                               (url_path (wd_location C1)))
                                             (SomeOrigin a!9)
                                             NoneOrigin))
                                  (a!12 (ite ((_ is url_path_blob)
                                               (url_path (wd_location C1)))
                                             a!11
                                             NoneOrigin))
                                  (a!23 (ite (= B1 4)
                                             a!19
                                             (ite (= B1 5)
                                                  a!20
                                                  (ite (= B1 6) a!21 a!22))))
                                  (a!30 (ite (or ((_ is ProtocolHTTPS)
                                                   (url_protocol I1))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol I1)))
                                             a!27
                                             (ite ((_ is ProtocolData)
                                                    (url_protocol I1))
                                                  a!28
                                                  a!29)))
                                  (a!39 (ite (= E 4)
                                             a!35
                                             (ite (= E 5)
                                                  a!36
                                                  (ite (= E 6) a!37 a!38))))
                                  (a!44 (ite (= (frame_window H) 3)
                                             (@3ArrayWindow (windows M))
                                             (ite (= (frame_window H) 4)
                                                  (@4ArrayWindow (windows M))
                                                  a!43)))
                                  (a!50 (or (and (c_csp_inherit_blob_from_creator
                                                   (config T))
                                                 a!49)
                                            (not (c_csp_inherit_blob_from_creator
                                                   (config T))))))
                            (let ((a!3 (ite (= F1 1)
                                            (Build_ArrayoptionBlob
                                              (@0ArrayoptionBlob H1)
                                              (SomeBlob G1)
                                              (@2ArrayoptionBlob H1)
                                              (@3ArrayoptionBlob H1)
                                              (@4ArrayoptionBlob H1)
                                              (@5ArrayoptionBlob H1)
                                              (@6ArrayoptionBlob H1)
                                              (@defaultArrayoptionBlob H1))
                                            (ite (= F1 2)
                                                 (Build_ArrayoptionBlob
                                                   (@0ArrayoptionBlob H1)
                                                   (@1ArrayoptionBlob H1)
                                                   (SomeBlob G1)
                                                   (@3ArrayoptionBlob H1)
                                                   (@4ArrayoptionBlob H1)
                                                   (@5ArrayoptionBlob H1)
                                                   (@6ArrayoptionBlob H1)
                                                   (@defaultArrayoptionBlob H1))
                                                 a!2)))
                                  (a!13 (ite ((_ is url_path_data)
                                               (url_path (wd_location C1)))
                                             NoneOrigin
                                             a!12))
                                  (a!24 (ite (= B1 1)
                                             a!16
                                             (ite (= B1 2)
                                                  a!17
                                                  (ite (= B1 3) a!18 a!23))))
                                  (a!40 (ite (= E 1)
                                             a!32
                                             (ite (= E 2)
                                                  a!33
                                                  (ite (= E 3) a!34 a!39))))
                                  (a!45 (ite (= (frame_window H) 1)
                                             (@1ArrayWindow (windows M))
                                             (ite (= (frame_window H) 2)
                                                  (@2ArrayWindow (windows M))
                                                  a!44))))
                            (let ((a!4 (= O1
                                          (ite (= F1 0)
                                               (Build_ArrayoptionBlob
                                                 (SomeBlob G1)
                                                 (@1ArrayoptionBlob H1)
                                                 (@2ArrayoptionBlob H1)
                                                 (@3ArrayoptionBlob H1)
                                                 (@4ArrayoptionBlob H1)
                                                 (@5ArrayoptionBlob H1)
                                                 (@6ArrayoptionBlob H1)
                                                 (@defaultArrayoptionBlob H1))
                                               a!3)))
                                  (a!14 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location C1)))
                                             a!10
                                             a!13))
                                  (a!25 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= B1 0)
                                                                 a!15
                                                                 a!24))))
                                  (a!26 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= B1 0)
                                                                 a!15
                                                                 a!24))))
                                  (a!41 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= E 0)
                                                                 a!31
                                                                 a!40))))
                                  (a!42 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= E 0)
                                                                 a!31
                                                                 a!40))))
                                  (a!46 (= (ite (= (frame_window H) 0)
                                                (@0ArrayWindow (windows M))
                                                a!45)
                                           K)))
                            (let ((a!47 (and (= (@0ContentElementFrame a!41) H)
                                             (= (@1ContentElementFrame a!41) G)
                                             (not ((_ is ContentElementScript)
                                                    a!41))
                                             (not ((_ is ContentElementImage)
                                                    a!41))
                                             (not ((_ is ContentElementHTML)
                                                    a!41))
                                             (not a!42)
                                             ((_ is SomeDOMElement)
                                               (ite (= E 0) a!31 a!40))
                                             (= S F)
                                             (= Q R)
                                             (= L Q)
                                             (= C1 L)
                                             (= K R)
                                             a!46
                                             (= Z D)
                                             (= D (DOMPath (consInt E I) J))
                                             (= O (DOMPath I J))
                                             (= O (DOMPath nilInt P))
                                             (= M N)
                                             (= T M))))
                            (let ((a!48 (or (and (= S Y)
                                                 (= X Y)
                                                 (= C1 X)
                                                 (= V (DOMPath nilInt W))
                                                 (= Z V)
                                                 (= T U))
                                            a!47)))
                            (let ((a!51 (and (Reachable T J1 A)
                                             (= A
                                                (Build_State K1
                                                             L1
                                                             M1
                                                             S
                                                             N1
                                                             H1
                                                             P1))
                                             (= B
                                                (Build_State (+ 1 K1)
                                                             L1
                                                             M1
                                                             S
                                                             N1
                                                             O1
                                                             P1))
                                             a!4
                                             (= (ite (= F1 0)
                                                     (@0ArrayoptionBlob H1)
                                                     a!6)
                                                NoneBlob)
                                             (= (url_path I1)
                                                (url_path_blob E1 F1))
                                             (= (blob_url G1) I1)
                                             (= E1 (blob_origin G1))
                                             (= (SomeOrigin (blob_origin G1))
                                                (ite a!7 a!8 a!14))
                                             (= (@0ContentElementScript a!25)
                                                D1)
                                             (= Z (DOMPath A1 (DOMIndex B1)))
                                             ((_ is SomeDOMElement)
                                               (ite (= B1 0) a!15 a!24))
                                             (not a!26)
                                             (not ((_ is ContentElementHTML)
                                                    a!25))
                                             (not ((_ is ContentElementImage)
                                                    a!25))
                                             a!30
                                             ((_ is ContentElementScript) a!25)
                                             a!48
                                             a!50
                                             (= C
                                                (consEvent (EvScriptCreateBlobUrl
                                                             Z
                                                             I1)
                                                           J1)))))
                              (=> a!51 (Reachable T C B)))))))))
                            :weight 0))))
      (a!128 (asserted (forall ((A Global))
                         (! (let ((a!1 (Build_URL ProtocolHTTP
                                                  (SomeDomain (subdomain 21 22))
                                                  (SomeInt 74)
                                                  (url_path_res (anypath 72))))
                                  (a!2 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            100
                                                                            (SomeInt 101)
                                                                            NonePath))
                                                  (SomeTrustedTypes (Build_TrustedTypes
                                                                      NoneoptionInt
                                                                      false))))
                                  (a!5 (Build_URL ProtocolHTTP
                                                  (SomeDomain (subdomain 21 22))
                                                  (SomeInt 48)
                                                  (url_path_res (anypath 86))))
                                  (a!6 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            (SomeoptionInt NoneInt)
                                                                            22
                                                                            NoneInt
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                  (a!8 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 112)
                                                                             (url_path_data 113
                                                                                            114)))))
                                  (a!9 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 115)
                                                                             (url_path_data 116
                                                                                            117)))))
                                  (a!10 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 118)
                                                                              (url_path_data 119
                                                                                             120)))))
                                  (a!11 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 121)
                                                                              (url_path_data 122
                                                                                             123)))))
                                  (a!12 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 124)
                                                                               (url_path_data 125
                                                                                              126)))))
                                  (a!13 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 127)
                                                                              (url_path_data 128
                                                                                             129)))))
                                  (a!14 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 109)
                                                                              (url_path_data 110
                                                                                             111)))))
                                  (a!17 (Build_URL ProtocolHTTP
                                                   (SomeDomain (subdomain 21 22))
                                                   (SomeInt 48)
                                                   (url_path_res (anypath 49))))
                                  (a!18 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                  (SomeoptionInt (SomeInt 21))
                                                                  22
                                                                  NoneInt
                                                                  NonePath)))
                                  (a!19 (SomeTrustedTypes (Build_TrustedTypes
                                                            (SomeoptionInt (SomeInt 53))
                                                            false)))
                                  (a!21 (Build_URL ProtocolHTTP
                                                   (SomeDomain (subdomain 21 22))
                                                   (SomeInt 56)
                                                   (url_path_res (anypath 57))))
                                  (a!22 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 58)
                                                                              (url_path_data 59
                                                                                             60)))))
                                  (a!23 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 61)
                                                                              (url_path_data 62
                                                                                             63)))))
                                  (a!24 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 64)
                                                                               (url_path_data 65
                                                                                              66)))))
                                  (a!25 (SomeHTMLElement (HTMLForm MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 67)
                                                                              (url_path_data 68
                                                                                             69)))))
                                  (a!28 (Build_RequestHeaders
                                          NoneOrigin
                                          (Build_ArrayoptionCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping
                                            NoneCookieMapping)
                                          NoneURL))
                                  (a!29 (Build_ArrayoptionCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          (SomeCookieMapping
                                            (Build_CookieMapping
                                              (NoPrefix 70)
                                              75))
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping))
                                  (a!30 (pairOriginoptionCSP
                                          (TupleOrigin ProtocolHTTP
                                                       (SomeDomain (domain 0))
                                                       (SomeInt 0))
                                          NoneCSP))
                                  (a!31 (distinct (@0pairOriginoptionCSP
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
                                                    (@5ArrayprodOriginoptionCSP
                                                      (origin_csp A)))
                                                  (@0pairOriginoptionCSP
                                                    (@6ArrayprodOriginoptionCSP
                                                      (origin_csp A)))
                                                  (@0pairOriginoptionCSP
                                                    (@defaultArrayprodOriginoptionCSP
                                                      (origin_csp A)))))
                                  (a!32 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 112)
                                                                               (url_path_data 113
                                                                                              114)))))
                                  (a!33 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 115)
                                                                               (url_path_data 116
                                                                                              117)))))
                                  (a!34 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 118)
                                                                               (url_path_data 119
                                                                                              120)))))
                                  (a!35 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 121)
                                                                               (url_path_data 122
                                                                                              123)))))
                                  (a!36 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 127)
                                                                               (url_path_data 128
                                                                                              129)))))
                                  (a!37 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 109)
                                                                               (url_path_data 110
                                                                                              111)))))
                                  (a!38 (Build_Initiators NoneInt
                                                          (Build_ArrayoptionInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt
                                                            NoneInt)))
                                  (a!44 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 58)
                                                                               (url_path_data 59
                                                                                              60)))))
                                  (a!45 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 61)
                                                                               (url_path_data 62
                                                                                              63)))))
                                  (a!46 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 67)
                                                                               (url_path_data 68
                                                                                              69)))))
                                  (a!51 (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                                                        71
                                                                        NoneDomain
                                                                        (subdomain 21
                                                                                   22)
                                                                        (anypath 72)
                                                                        false
                                                                        false
                                                                        SSStrict)))
                                  (a!52 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                             NoneoptionInt
                                                                             95
                                                                             (SomeInt 96)
                                                                             NonePath))
                                                   NoneTrustedTypes))
                                  (a!64 (Build_ArrayoptionprodprodEmitterIntInt
                                          NoneprodprodEmitterIntInt
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 0)
                                              0))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 1)
                                              1))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 2)
                                              2))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 3)
                                              3))
                                          NoneprodprodEmitterIntInt
                                          NoneprodprodEmitterIntInt
                                          NoneprodprodEmitterIntInt))
                                  (a!66 (Build_ServiceWorker
                                          0
                                          (Build_ArrayoptionInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt))))
                            (let ((a!3 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeScript)
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 97)
                                                             (url_path_data 98
                                                                            99)))
                                         (SomeCSP a!2)
                                         NoneReferrerPolicy))
                                  (a!7 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                                                         75
                                                                         NoneDomain
                                                                         (subdomain 21
                                                                                    22)
                                                                         (anypath 72)
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 102))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 103)
                                                             (url_path_data 104
                                                                            105)))
                                         (SomeCSP a!6)
                                         NoneReferrerPolicy))
                                  (a!15 (Build_HTML 107
                                                    108
                                                    (Build_ArrayoptionHTMLElement
                                                      a!8
                                                      (SomeHTMLElement (HTMLScript a!1))
                                                      a!9
                                                      a!10
                                                      a!11
                                                      a!12
                                                      a!13
                                                      a!14)))
                                  (a!20 (Build_ResponseHeaders
                                          (SomeContentType ContentTypeHTML)
                                          NoneSetCookie
                                          NoneOrigin
                                          (SomeURL (Build_URL ProtocolHTTP
                                                              NoneDomain
                                                              (SomeInt 50)
                                                              (url_path_data 51
                                                                             52)))
                                          (SomeCSP (Build_CSP a!18 a!19))
                                          NoneReferrerPolicy))
                                  (a!26 (Build_HTML 54
                                                    55
                                                    (Build_ArrayoptionHTMLElement
                                                      (SomeHTMLElement (HTMLFrame a!5))
                                                      (SomeHTMLElement (HTMLScript a!21))
                                                      a!22
                                                      a!23
                                                      a!24
                                                      NoneHTMLElement
                                                      a!25
                                                      NoneHTMLElement)))
                                  (a!40 (SomeDOMElement (DOMElementResource
                                                          a!1
                                                          (ContentElementScript
                                                            (Build_Script a!1 8)))))
                                  (a!43 (SomeDOMElement (DOMElementResource
                                                          a!21
                                                          (ContentElementScript
                                                            (Build_Script a!21
                                                                          11)))))
                                  (a!53 (Build_ResponseHeaders
                                          (SomeContentType ContentTypeScript)
                                          a!51
                                          NoneOrigin
                                          (SomeURL (Build_URL ProtocolHTTP
                                                              NoneDomain
                                                              (SomeInt 92)
                                                              (url_path_data 93
                                                                             94)))
                                          (SomeCSP a!52)
                                          NoneReferrerPolicy)))
                            (let ((a!4 (Build_Response a!1
                                                       ResponseOk
                                                       a!3
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!1 8)))))
                                  (a!16 (Build_Response a!5
                                                        ResponseOk
                                                        a!7
                                                        (SomeContentElement
                                                          (ContentElementFrame
                                                            (Build_Frame a!5
                                                                         106)
                                                            a!15))))
                                  (a!27 (= (@0ArrayResponse (responses A))
                                           (Build_Response a!17
                                                           ResponseOk
                                                           a!20
                                                           (SomeContentElement
                                                             (ContentElementHTML
                                                               a!26)))))
                                  (a!39 (Build_Document 6
                                                        2
                                                        a!7
                                                        a!15
                                                        (Build_DOM 2
                                                                   0
                                                                   (Build_ArrayoptionDOMElement
                                                                     (SomeDOMElement a!32)
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!33)
                                                                     (SomeDOMElement a!34)
                                                                     (SomeDOMElement a!35)
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!36)
                                                                     (SomeDOMElement a!37)))
                                                        a!38))
                                  (a!41 (Build_Document 9
                                                        2
                                                        a!7
                                                        a!15
                                                        (Build_DOM 2
                                                                   0
                                                                   (Build_ArrayoptionDOMElement
                                                                     (SomeDOMElement a!32)
                                                                     a!40
                                                                     (SomeDOMElement a!33)
                                                                     (SomeDOMElement a!34)
                                                                     (SomeDOMElement a!35)
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!36)
                                                                     (SomeDOMElement a!37)))
                                                        a!38))
                                  (a!42 (SomeDOMElement (DOMElementResource
                                                          a!1
                                                          (ContentElementFrame
                                                            (Build_Frame a!5 5)
                                                            a!15))))
                                  (a!48 (SomeDOMElement (DOMElementResource
                                                          a!5
                                                          (ContentElementFrame
                                                            (Build_Frame a!5
                                                                         106)
                                                            a!15))))
                                  (a!50 (Build_Document 3
                                                        1
                                                        a!20
                                                        a!26
                                                        (Build_DOM 1
                                                                   0
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!44)
                                                                     (SomeDOMElement a!45)
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!46)
                                                                     NoneDOMElement))
                                                        a!38))
                                  (a!54 (Build_Response a!21
                                                        ResponseOk
                                                        a!53
                                                        (SomeContentElement
                                                          (ContentElementScript
                                                            (Build_Script a!21
                                                                          11)))))
                                  (a!56 (EvResponse (Build_Response a!17
                                                                    ResponseOk
                                                                    a!20
                                                                    (SomeContentElement
                                                                      (ContentElementHTML
                                                                        a!26)))
                                                    1)))
                            (let ((a!47 (Build_Document 12
                                                        1
                                                        a!20
                                                        a!26
                                                        (Build_DOM 1
                                                                   0
                                                                   (Build_ArrayoptionDOMElement
                                                                     a!42
                                                                     a!43
                                                                     (SomeDOMElement a!44)
                                                                     (SomeDOMElement a!45)
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!46)
                                                                     NoneDOMElement))
                                                        a!38))
                                  (a!49 (Build_Document 6
                                                        1
                                                        a!20
                                                        a!26
                                                        (Build_DOM 1
                                                                   0
                                                                   (Build_ArrayoptionDOMElement
                                                                     a!48
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!44)
                                                                     (SomeDOMElement a!45)
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!46)
                                                                     NoneDOMElement))
                                                        a!38))
                                  (a!57 (consEvent a!56
                                                   (consEvent (EvRequest EmitterClient
                                                                         (Build_Request MethodGet
                                                                                        a!17
                                                                                        a!28
                                                                                        NoneInt)
                                                                         1)
                                                              nilEvent)))
                                  (a!65 (Build_FetchEngine
                                          11
                                          EmitterClient
                                          (Build_Request MethodGet
                                                         a!21
                                                         a!28
                                                         NoneInt)
                                          4
                                          (SomeResponse a!54)
                                          a!64)))
                            (let ((a!55 (and (= (@2ArrayResponse (responses A))
                                                a!4)
                                             (= (@1ArrayResponse (responses A))
                                                a!16)
                                             a!27
                                             (= (@3ArrayRequest (requests A))
                                                (Build_Request MethodGet
                                                               a!21
                                                               a!28
                                                               NoneInt))
                                             (= (@2ArrayRequest (requests A))
                                                (Build_Request MethodGet
                                                               a!1
                                                               (Build_RequestHeaders
                                                                 NoneOrigin
                                                                 a!29
                                                                 NoneURL)
                                                               NoneInt))
                                             (= (@1ArrayRequest (requests A))
                                                (Build_Request MethodGet
                                                               a!5
                                                               a!28
                                                               NoneInt))
                                             (= (@0ArrayRequest (requests A))
                                                (Build_Request MethodGet
                                                               a!17
                                                               a!28
                                                               NoneInt))
                                             (= (@0ArrayprodOriginoptionCSP
                                                  (origin_csp A))
                                                a!30)
                                             a!31
                                             (distinct (@0ArrayResponse (responses A))
                                                       (@1ArrayResponse (responses A))
                                                       (@2ArrayResponse (responses A))
                                                       (@3ArrayResponse (responses A))
                                                       (@4ArrayResponse (responses A))
                                                       (@5ArrayResponse (responses A))
                                                       (@6ArrayResponse (responses A))
                                                       (@defaultArrayResponse
                                                         (responses A)))
                                             (distinct (@0ArrayRequest (requests A))
                                                       (@1ArrayRequest (requests A))
                                                       (@2ArrayRequest (requests A))
                                                       (@3ArrayRequest (requests A))
                                                       (@4ArrayRequest (requests A))
                                                       (@5ArrayRequest (requests A))
                                                       (@6ArrayRequest (requests A))
                                                       (@defaultArrayRequest
                                                         (requests A)))
                                             (= (@defaultArrayWindow
                                                  (windows A))
                                                (Build_Window 2
                                                              (SomeInt 2)
                                                              a!5
                                                              NoneDomain
                                                              a!39))
                                             (= (@5ArrayWindow (windows A))
                                                (Build_Window 2
                                                              (SomeInt 2)
                                                              a!5
                                                              NoneDomain
                                                              a!41))
                                             (= (@4ArrayWindow (windows A))
                                                (Build_Window 1
                                                              NoneInt
                                                              a!17
                                                              NoneDomain
                                                              a!47))
                                             (= (@2ArrayWindow (windows A))
                                                (Build_Window 1
                                                              NoneInt
                                                              a!17
                                                              NoneDomain
                                                              a!49))
                                             (= (@0ArrayWindow (windows A))
                                                (Build_Window 1
                                                              NoneInt
                                                              a!17
                                                              NoneDomain
                                                              a!50))
                                             (= (@3ArrayInt (server_responses A))
                                                3)
                                             (= (@2ArrayInt (server_responses A))
                                                2)
                                             (= (@1ArrayInt (server_responses A))
                                                1)
                                             (= (@0ArrayInt (server_responses A))
                                                0)
                                             (not (c_origin_wide_csp (config A)))
                                             (= (@3ArrayResponse (responses A))
                                                a!54)))
                                  (a!58 (consEvent (EvRequest EmitterClient
                                                              (Build_Request MethodGet
                                                                             a!5
                                                                             a!28
                                                                             NoneInt)
                                                              2)
                                                   (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                                    DOMTopLevel))
                                                              a!57)))
                                  (a!67 (Build_State 12
                                                     a!65
                                                     a!66
                                                     (Build_Window 1
                                                                   NoneInt
                                                                   a!17
                                                                   NoneDomain
                                                                   a!47)
                                                     (Build_ArrayoptionSetCookie
                                                       NoneSetCookie
                                                       a!51
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
                                                       NoneBlob
                                                       NoneBlob
                                                       NoneBlob)
                                                     (Build_ArrayoptionStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem))))
                            (let ((a!59 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                         (DOMIndex 0)))
                                                   (consEvent (EvResponse a!16
                                                                          2)
                                                              a!58))))
                            (let ((a!60 (consEvent (EvRequest EmitterClient
                                                              (Build_Request MethodGet
                                                                             a!1
                                                                             (Build_RequestHeaders
                                                                               NoneOrigin
                                                                               a!29
                                                                               NoneURL)
                                                                             NoneInt)
                                                              3)
                                                   a!59)))
                            (let ((a!61 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                                  nilInt)
                                                                         (DOMIndex 1)))
                                                   (consEvent (EvResponse a!4 3)
                                                              a!60))))
                            (let ((a!62 (consEvent (EvResponse a!54 4)
                                                   (consEvent (EvRequest EmitterClient
                                                                         (Build_Request MethodGet
                                                                                        a!21
                                                                                        a!28
                                                                                        NoneInt)
                                                                         4)
                                                              a!61))))
                            (let ((a!63 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                         (DOMIndex 1)))
                                                   a!62)))
                              (=> a!55 (Reachable A a!63 a!67))))))))))))
                            :weight 0)))))
(let ((a!2 (hyper-res a!1
                      (forall ((A NestedDOMPath)
                               (B Bool)
                               (C Bool)
                               (D HTML)
                               (E Bool)
                               (F Bool)
                               (G Bool)
                               (H Window)
                               (I Window)
                               (J Bool)
                               (K Global)
                               (L NestedDOMPath)
                               (M Bool)
                               (N Window)
                               (O Window)
                               (P Bool)
                               (Q Bool)
                               (R Bool)
                               (S Bool)
                               (T Bool)
                               (U Bool)
                               (V Bool)
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
                               (G1 Bool))
                        (! (let ((a!1 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 21 22))
                                                 (SomeInt 48)
                                                 (url_path_res (anypath 49))))
                                 (a!2 (Build_RequestHeaders
                                        NoneOrigin
                                        (Build_ArrayoptionCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping
                                          NoneCookieMapping)
                                        NoneURL))
                                 (a!3 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 21 22))
                                                 (SomeInt 48)
                                                 (url_path_res (anypath 86))))
                                 (a!4 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 21 22))
                                                 (SomeInt 74)
                                                 (url_path_res (anypath 72))))
                                 (a!5 (Build_ArrayoptionCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        (SomeCookieMapping
                                          (Build_CookieMapping (NoPrefix 70) 75))
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping
                                        NoneCookieMapping))
                                 (a!6 (Build_URL ProtocolHTTP
                                                 (SomeDomain (subdomain 21 22))
                                                 (SomeInt 56)
                                                 (url_path_res (anypath 57))))
                                 (a!7 (url_path_blob (TupleOrigin ProtocolHTTP
                                                                  (SomeDomain (subdomain 21
                                                                                         22))
                                                                  (SomeInt 48))
                                                     2))
                                 (a!9 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                (SomeoptionInt (SomeInt 21))
                                                                22
                                                                NoneInt
                                                                NonePath)))
                                 (a!10 (SomeTrustedTypes (Build_TrustedTypes
                                                           (SomeoptionInt (SomeInt 53))
                                                           false)))
                                 (a!12 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 58)
                                                                             (url_path_data 59
                                                                                            60)))))
                                 (a!13 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 61)
                                                                             (url_path_data 62
                                                                                            63)))))
                                 (a!14 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 64)
                                                                              (url_path_data 65
                                                                                             66)))))
                                 (a!15 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 67)
                                                                             (url_path_data 68
                                                                                            69)))))
                                 (a!17 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            (SomeoptionInt NoneInt)
                                                                            22
                                                                            NoneInt
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                 (a!19 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 112)
                                                                             (url_path_data 113
                                                                                            114)))))
                                 (a!20 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 115)
                                                                             (url_path_data 116
                                                                                            117)))))
                                 (a!21 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 118)
                                                                             (url_path_data 119
                                                                                            120)))))
                                 (a!22 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 121)
                                                                             (url_path_data 122
                                                                                            123)))))
                                 (a!23 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 124)
                                                                              (url_path_data 125
                                                                                             126)))))
                                 (a!24 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 127)
                                                                             (url_path_data 128
                                                                                            129)))))
                                 (a!25 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 109)
                                                                             (url_path_data 110
                                                                                            111)))))
                                 (a!28 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            100
                                                                            (SomeInt 101)
                                                                            NonePath))
                                                  (SomeTrustedTypes (Build_TrustedTypes
                                                                      NoneoptionInt
                                                                      false))))
                                 (a!31 (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                                                       71
                                                                       NoneDomain
                                                                       (subdomain 21
                                                                                  22)
                                                                       (anypath 72)
                                                                       false
                                                                       false
                                                                       SSStrict)))
                                 (a!32 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            95
                                                                            (SomeInt 96)
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                 (a!35 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 69299)
                                                                         19483
                                                                         NoneDomain
                                                                         (domain 69843)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 68628))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 69426)
                                                             (url_path_data 69841
                                                                            69842)))
                                         NoneCSP
                                         NoneReferrerPolicy))
                                 (a!36 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 69038
                                                       69039
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!38 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 46474)
                                                                             (url_path_data 51817
                                                                                            51818)))))
                                 (a!39 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 47350)
                                                                             (url_path_data 45324
                                                                                            45325)))))
                                 (a!40 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 42965)
                                                                             (url_path_data 65937
                                                                                            65938)))))
                                 (a!41 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 41304)
                                                                              (url_path_data 59279
                                                                                             59280)))))
                                 (a!42 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 58483)
                                                                              (url_path_data 64739
                                                                                             64740)))))
                                 (a!43 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 38025)
                                                                              (url_path_data 49543
                                                                                             49544)))))
                                 (a!46 (Build_ResponseHeaders
                                         NoneContentType
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 69180)
                                                             (url_path_data 70021
                                                                            70022)))
                                         NoneCSP
                                         NoneReferrerPolicy))
                                 (a!47 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 70363
                                                       70364
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!48 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 69743)
                                                                         19484
                                                                         NoneDomain
                                                                         (domain 69507)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 43848))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 70480)
                                                             (url_path_data 69620
                                                                            69621)))
                                         NoneCSP
                                         NoneReferrerPolicy))
                                 (a!49 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 70428
                                                       70429
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!52 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 72723)
                                                                               (url_path_data 74376
                                                                                              74377))
                                                                    69193)))
                                 (a!53 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 72512)
                                                                               (url_path_data 72935
                                                                                              72936))
                                                                    69719)))
                                 (a!54 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 58)
                                                                              (url_path_data 59
                                                                                             60)))))
                                 (a!55 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 61)
                                                                              (url_path_data 62
                                                                                             63)))))
                                 (a!56 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 67)
                                                                              (url_path_data 68
                                                                                             69)))))
                                 (a!57 (Build_Initiators NoneInt
                                                         (Build_ArrayoptionInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt)))
                                 (a!62 (Build_Initiators NoneInt
                                                         (Build_ArrayoptionInt
                                                           (SomeInt 5)
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt
                                                           NoneInt)))
                                 (a!66 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 73999)
                                                                              (url_path_data 75143
                                                                                             75144)))))
                                 (a!67 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 73366)
                                                                              (url_path_data 74530
                                                                                             74531)))))
                                 (a!68 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 72495)
                                                                              (url_path_data 73603
                                                                                             73604)))))
                                 (a!69 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 72346)
                                                                              (url_path_data 74267
                                                                                             74268)))))
                                 (a!70 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 72251)
                                                                              (url_path_data 74817
                                                                                             74818)))))
                                 (a!71 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 73445)
                                                                              (url_path_data 72715
                                                                                             72716)))))
                                 (a!72 (SomeHTMLElement (HTMLImage (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 72354)
                                                                              (url_path_data 72668
                                                                                             72669)))))
                                 (a!76 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 112)
                                                                              (url_path_data 113
                                                                                             114)))))
                                 (a!78 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 115)
                                                                              (url_path_data 116
                                                                                             117)))))
                                 (a!79 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 118)
                                                                              (url_path_data 119
                                                                                             120)))))
                                 (a!80 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 121)
                                                                              (url_path_data 122
                                                                                             123)))))
                                 (a!81 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 127)
                                                                              (url_path_data 128
                                                                                             129)))))
                                 (a!82 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 109)
                                                                              (url_path_data 110
                                                                                             111)))))
                                 (a!84 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 46474)
                                                                              (url_path_data 51817
                                                                                             51818)))))
                                 (a!85 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 47350)
                                                                              (url_path_data 45324
                                                                                             45325)))))
                                 (a!86 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 42965)
                                                                              (url_path_data 65937
                                                                                             65938)))))
                                 (a!90 (Build_ArrayContentElement
                                         (ContentElementHTML
                                           (Build_HTML 35766
                                                       35767
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 24911
                                                       24912
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 24905
                                                       24906
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 38455
                                                       38456
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 41186
                                                       41187
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 62703
                                                       62704
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 20372
                                                       20373
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 21962
                                                       21963
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!91 (pairOriginoptionCSP
                                         (TupleOrigin ProtocolHTTP
                                                      (SomeDomain (domain 0))
                                                      (SomeInt 0))
                                         NoneCSP))
                                 (a!106 (Build_ArrayoptionprodprodEmitterIntInt
                                          NoneprodprodEmitterIntInt
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 0)
                                              0))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 1)
                                              1))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 2)
                                              2))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 3)
                                              3))
                                          (SomeprodprodEmitterIntInt
                                            (pairprodEmitterIntInt
                                              (pairEmitterInt EmitterClient 6)
                                              5))
                                          NoneprodprodEmitterIntInt
                                          NoneprodprodEmitterIntInt))
                                 (a!108 (Build_ServiceWorker
                                          0
                                          (Build_ArrayoptionInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt
                                            NoneInt)))
                                 (a!114 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 71649)
                                                                               (url_path_data 72222
                                                                                              72223)))))
                                 (a!115 (ContentElementFrame
                                          (Build_Frame (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 75359)
                                                                  (url_path_data 75310
                                                                                 75311))
                                                       71583)
                                          (Build_HTML 71584
                                                      71585
                                                      (Build_ArrayoptionHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement
                                                        NoneHTMLElement))))
                                 (a!117 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 74218)
                                                                               (url_path_data 73396
                                                                                              73397)))))
                                 (a!118 (DOMElementForm (Build_Form MethodGet
                                                                    (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 74485)
                                                                               (url_path_data 73887
                                                                                              73888)))))
                                 (a!132 (Build_Frame (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 20556)
                                                                (url_path_data 48028
                                                                               48029))
                                                     18912))
                                 (a!135 (Build_ArrayResponse
                                          (Build_Response (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 19603)
                                                                     (url_path_data 65747
                                                                                    65748))
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
                                                                     (SomeInt 57134)
                                                                     (url_path_data 46646
                                                                                    46647))
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
                                                                     (SomeInt 61091)
                                                                     (url_path_data 61625
                                                                                    61626))
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
                                                                     (SomeInt 41190)
                                                                     (url_path_data 65191
                                                                                    65192))
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
                                                                     (SomeInt 20374)
                                                                     (url_path_data 48631
                                                                                    48632))
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
                                                                     (SomeInt 19998)
                                                                     (url_path_data 23819
                                                                                    23820))
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
                                                                     (SomeInt 65184)
                                                                     (url_path_data 44088
                                                                                    44089))
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
                                                                     (SomeInt 44634)
                                                                     (url_path_data 45045
                                                                                    45046))
                                                          ResponseOk
                                                          (Build_ResponseHeaders
                                                            NoneContentType
                                                            NoneSetCookie
                                                            NoneOrigin
                                                            NoneURL
                                                            NoneCSP
                                                            NoneReferrerPolicy)
                                                          NoneContentElement)))
                                 (a!136 (Build_Document 18925
                                                        18926
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18921
                                                                    18922
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18923
                                                                   18924
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 57475)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 39343)
                                                                            (SomeInt 64554)
                                                                            (SomeInt 50009)
                                                                            (SomeInt 58999)
                                                                            (SomeInt 35794)
                                                                            (SomeInt 67751)
                                                                            (SomeInt 27489)
                                                                            (SomeInt 57065)))))
                                 (a!137 (Build_Document 18932
                                                        18933
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18928
                                                                    18929
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18930
                                                                   18931
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 51284)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 50368)
                                                                            (SomeInt 41353)
                                                                            (SomeInt 57593)
                                                                            (SomeInt 39438)
                                                                            (SomeInt 49043)
                                                                            (SomeInt 30054)
                                                                            (SomeInt 24406)
                                                                            (SomeInt 31753)))))
                                 (a!138 (Build_Document 18939
                                                        18940
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18935
                                                                    18936
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18937
                                                                   18938
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 26213)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 24806)
                                                                            (SomeInt 55240)
                                                                            (SomeInt 44884)
                                                                            (SomeInt 40628)
                                                                            (SomeInt 59723)
                                                                            (SomeInt 26760)
                                                                            (SomeInt 38071)
                                                                            (SomeInt 55453)))))
                                 (a!139 (Build_Document 18946
                                                        18947
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18942
                                                                    18943
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18944
                                                                   18945
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 32982)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 58540)
                                                                            (SomeInt 51986)
                                                                            (SomeInt 19657)
                                                                            (SomeInt 40675)
                                                                            (SomeInt 28626)
                                                                            (SomeInt 27458)
                                                                            (SomeInt 62022)
                                                                            (SomeInt 28551)))))
                                 (a!140 (Build_Document 18953
                                                        18954
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18949
                                                                    18950
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18951
                                                                   18952
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 25674)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 53766)
                                                                            (SomeInt 21457)
                                                                            (SomeInt 44337)
                                                                            (SomeInt 62202)
                                                                            (SomeInt 46119)
                                                                            (SomeInt 37064)
                                                                            (SomeInt 37593)
                                                                            (SomeInt 57275)))))
                                 (a!141 (Build_Document 18960
                                                        18961
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18956
                                                                    18957
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18958
                                                                   18959
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 50057)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 28975)
                                                                            (SomeInt 30886)
                                                                            (SomeInt 65062)
                                                                            (SomeInt 65431)
                                                                            (SomeInt 38933)
                                                                            (SomeInt 61747)
                                                                            (SomeInt 36515)
                                                                            (SomeInt 53639)))))
                                 (a!142 (Build_Document 18967
                                                        18968
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18963
                                                                    18964
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18965
                                                                   18966
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 66182)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 49450)
                                                                            (SomeInt 23886)
                                                                            (SomeInt 19557)
                                                                            (SomeInt 65196)
                                                                            (SomeInt 59862)
                                                                            (SomeInt 56520)
                                                                            (SomeInt 53641)
                                                                            (SomeInt 31754)))))
                                 (a!143 (Build_Document 18974
                                                        18975
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18970
                                                                    18971
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18972
                                                                   18973
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 47897)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 52961)
                                                                            (SomeInt 64495)
                                                                            (SomeInt 63713)
                                                                            (SomeInt 29960)
                                                                            (SomeInt 31695)
                                                                            (SomeInt 68304)
                                                                            (SomeInt 67845)
                                                                            (SomeInt 50819)))))
                                 (a!145 (Build_ArrayContentElement
                                          (ContentElementHTML
                                            (Build_HTML 40790
                                                        40791
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 63077
                                                        63078
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 50285
                                                        50286
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 47042
                                                        47043
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 35653
                                                        35654
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 45459
                                                        45460
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 50929
                                                        50930
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement)))
                                          (ContentElementHTML
                                            (Build_HTML 50010
                                                        50011
                                                        (Build_ArrayoptionHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement
                                                          NoneHTMLElement))))))
                           (let ((a!8 (Build_ArrayRequest
                                        (Build_Request MethodGet
                                                       a!1
                                                       a!2
                                                       NoneInt)
                                        (Build_Request MethodGet
                                                       a!3
                                                       a!2
                                                       NoneInt)
                                        (Build_Request MethodGet
                                                       a!4
                                                       (Build_RequestHeaders
                                                         NoneOrigin
                                                         a!5
                                                         NoneURL)
                                                       NoneInt)
                                        (Build_Request MethodGet
                                                       a!6
                                                       a!2
                                                       NoneInt)
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolBlob
                                                                  NoneDomain
                                                                  (SomeInt 20463)
                                                                  (url_path_data 2552
                                                                                 19503))
                                                       a!2
                                                       (SomeInt 24537))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 63108)
                                                                  (url_path_data 64564
                                                                                 64565))
                                                       a!2
                                                       (SomeInt 35099))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolBlob
                                                                  NoneDomain
                                                                  NoneInt
                                                                  a!7)
                                                       a!2
                                                       NoneInt)
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 23392)
                                                                  (url_path_res slash))
                                                       a!2
                                                       (SomeInt 58160))))
                                 (a!11 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 50)
                                                             (url_path_data 51
                                                                            52)))
                                         (SomeCSP (Build_CSP a!9 a!10))
                                         NoneReferrerPolicy))
                                 (a!16 (Build_HTML 54
                                                   55
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!3))
                                                     (SomeHTMLElement (HTMLScript a!6))
                                                     a!12
                                                     a!13
                                                     a!14
                                                     NoneHTMLElement
                                                     a!15
                                                     NoneHTMLElement)))
                                 (a!18 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                                                         75
                                                                         NoneDomain
                                                                         (subdomain 21
                                                                                    22)
                                                                         (anypath 72)
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 102))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 103)
                                                             (url_path_data 104
                                                                            105)))
                                         (SomeCSP a!17)
                                         NoneReferrerPolicy))
                                 (a!26 (Build_HTML 107
                                                   108
                                                   (Build_ArrayoptionHTMLElement
                                                     a!19
                                                     (SomeHTMLElement (HTMLScript a!4))
                                                     a!20
                                                     a!21
                                                     a!22
                                                     a!23
                                                     a!24
                                                     a!25)))
                                 (a!29 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeScript)
                                         NoneSetCookie
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 97)
                                                             (url_path_data 98
                                                                            99)))
                                         (SomeCSP a!28)
                                         NoneReferrerPolicy))
                                 (a!33 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeScript)
                                         a!31
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 92)
                                                             (url_path_data 93
                                                                            94)))
                                         (SomeCSP a!32)
                                         NoneReferrerPolicy))
                                 (a!37 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         NoneSetCookie
                                         NoneOrigin
                                         NoneURL
                                         (SomeCSP (Build_CSP a!9 a!10))
                                         NoneReferrerPolicy))
                                 (a!44 (Build_HTML 12766
                                                   12767
                                                   (Build_ArrayoptionHTMLElement
                                                     NoneHTMLElement
                                                     a!38
                                                     a!39
                                                     a!40
                                                     a!41
                                                     NoneHTMLElement
                                                     a!42
                                                     a!43)))
                                 (a!50 (Build_Response (Build_URL ProtocolHTTP
                                                                  (SomeDomain (domain 69452))
                                                                  (SomeInt 35652)
                                                                  (url_path_data 46047
                                                                                 46048))
                                                       ResponseOk
                                                       a!48
                                                       a!49))
                                 (a!59 (Build_ArrayoptionHTMLElement
                                         (SomeHTMLElement (HTMLFrame (Build_URL ProtocolBlob
                                                                                NoneDomain
                                                                                NoneInt
                                                                                a!7)))
                                         (SomeHTMLElement (HTMLScript a!6))
                                         a!12
                                         a!13
                                         a!14
                                         NoneHTMLElement
                                         a!15
                                         NoneHTMLElement))
                                 (a!61 (SomeDOMElement (DOMElementResource
                                                         a!6
                                                         (ContentElementScript
                                                           (Build_Script a!6 11)))))
                                 (a!73 (Build_Document 12763
                                                       12764
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 12759
                                                                   12760
                                                                   (Build_ArrayoptionHTMLElement
                                                                     a!66
                                                                     a!67
                                                                     a!68
                                                                     a!69
                                                                     a!70
                                                                     NoneHTMLElement
                                                                     a!71
                                                                     a!72))
                                                       (Build_DOM 12761
                                                                  12762
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 36476)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 29506)
                                                                           (SomeInt 24857)
                                                                           (SomeInt 51228)
                                                                           (SomeInt 62306)
                                                                           (SomeInt 19925)
                                                                           (SomeInt 29652)
                                                                           (SomeInt 64751)
                                                                           (SomeInt 52029)))))
                                 (a!77 (SomeDOMElement (DOMElementResource
                                                         a!4
                                                         (ContentElementScript
                                                           (Build_Script a!4 8)))))
                                 (a!116 (SomeDOMElement (DOMElementResource
                                                          (Build_URL ProtocolHTTP
                                                                     NoneDomain
                                                                     (SomeInt 69463)
                                                                     (url_path_data 69711
                                                                                    69712))
                                                          a!115)))
                                 (a!134 (Build_ArrayRequest
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 59355)
                                                                    (url_path_data 64526
                                                                                   64527))
                                                         a!2
                                                         (SomeInt 24183))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 36737)
                                                                    (url_path_data 59959
                                                                                   59960))
                                                         a!2
                                                         (SomeInt 60113))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 61823)
                                                                    (url_path_data 32928
                                                                                   32929))
                                                         a!2
                                                         (SomeInt 56030))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 32322)
                                                                    (url_path_data 60714
                                                                                   60715))
                                                         a!2
                                                         (SomeInt 45811))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 61360)
                                                                    (url_path_data 61298
                                                                                   61299))
                                                         a!2
                                                         (SomeInt 42173))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 32370)
                                                                    (url_path_data 55684
                                                                                   55685))
                                                         a!2
                                                         (SomeInt 42017))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 51582)
                                                                    (url_path_data 65768
                                                                                   65769))
                                                         a!2
                                                         (SomeInt 66967))
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 39995)
                                                                    (url_path_data 51106
                                                                                   51107))
                                                         a!2
                                                         (SomeInt 65083))))
                                 (a!144 (Build_ArrayWindow
                                          (Build_Window 18927
                                                        (SomeInt 54865)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 35083)
                                                                   (url_path_data 57137
                                                                                  57138))
                                                        NoneDomain
                                                        a!136)
                                          (Build_Window 18934
                                                        (SomeInt 20506)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 40959)
                                                                   (url_path_data 39894
                                                                                  39895))
                                                        NoneDomain
                                                        a!137)
                                          (Build_Window 18941
                                                        (SomeInt 34670)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 46440)
                                                                   (url_path_data 21455
                                                                                  21456))
                                                        NoneDomain
                                                        a!138)
                                          (Build_Window 18948
                                                        (SomeInt 59175)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 39083)
                                                                   (url_path_data 20464
                                                                                  20465))
                                                        NoneDomain
                                                        a!139)
                                          (Build_Window 18955
                                                        (SomeInt 48244)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 48160)
                                                                   (url_path_data 49397
                                                                                  49398))
                                                        NoneDomain
                                                        a!140)
                                          (Build_Window 18962
                                                        (SomeInt 28293)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 63133)
                                                                   (url_path_data 35590
                                                                                  35591))
                                                        NoneDomain
                                                        a!141)
                                          (Build_Window 18969
                                                        (SomeInt 30342)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 51721)
                                                                   (url_path_data 44958
                                                                                  44959))
                                                        NoneDomain
                                                        a!142)
                                          (Build_Window 18976
                                                        (SomeInt 42451)
                                                        (Build_URL ProtocolHTTP
                                                                   NoneDomain
                                                                   (SomeInt 56156)
                                                                   (url_path_data 30963
                                                                                  30964))
                                                        NoneDomain
                                                        a!143))))
                           (let ((a!27 (Build_Response a!3
                                                       ResponseOk
                                                       a!18
                                                       (SomeContentElement
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 106)
                                                           a!26))))
                                 (a!30 (Build_Response a!4
                                                       ResponseOk
                                                       a!29
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!4 8)))))
                                 (a!34 (Build_Response a!6
                                                       ResponseOk
                                                       a!33
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!6 11)))))
                                 (a!45 (SomeContentElement
                                         (ContentElementFrame
                                           (Build_Frame (Build_URL ProtocolBlob
                                                                   NoneDomain
                                                                   NoneInt
                                                                   a!7)
                                                        6)
                                           a!44)))
                                 (a!58 (Build_Document 3
                                                       1
                                                       a!11
                                                       a!16
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!54)
                                                                    (SomeDOMElement a!55)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!56)
                                                                    NoneDOMElement))
                                                       a!57))
                                 (a!60 (DOMElementResource
                                         (Build_URL ProtocolBlob
                                                    NoneDomain
                                                    NoneInt
                                                    a!7)
                                         (ContentElementFrame
                                           (Build_Frame (Build_URL ProtocolBlob
                                                                   NoneDomain
                                                                   NoneInt
                                                                   a!7)
                                                        6)
                                           a!44)))
                                 (a!64 (SomeDOMElement (DOMElementResource
                                                         a!3
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 106)
                                                           a!26))))
                                 (a!74 (SomeDOMElement (DOMElementResource
                                                         a!4
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 5)
                                                           a!26))))
                                 (a!83 (Build_Document 9
                                                       2
                                                       a!18
                                                       a!26
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    (SomeDOMElement a!76)
                                                                    a!77
                                                                    (SomeDOMElement a!78)
                                                                    (SomeDOMElement a!79)
                                                                    (SomeDOMElement a!80)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!81)
                                                                    (SomeDOMElement a!82)))
                                                       a!57))
                                 (a!87 (Build_Document 17
                                                       5
                                                       a!37
                                                       a!44
                                                       (Build_DOM 5
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!84)
                                                                    (SomeDOMElement a!85)
                                                                    (SomeDOMElement a!86)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       a!57))
                                 (a!88 (Build_Document 6
                                                       2
                                                       a!18
                                                       a!26
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    (SomeDOMElement a!76)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!78)
                                                                    (SomeDOMElement a!79)
                                                                    (SomeDOMElement a!80)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!81)
                                                                    (SomeDOMElement a!82)))
                                                       a!57))
                                 (a!93 (EvResponse (Build_Response a!1
                                                                   ResponseOk
                                                                   a!11
                                                                   (SomeContentElement
                                                                     (ContentElementHTML
                                                                       a!16)))
                                                   1))
                                 (a!109 (Build_Blob (Build_URL ProtocolBlob
                                                               NoneDomain
                                                               NoneInt
                                                               a!7)
                                                    (ContentElementFrame
                                                      (Build_Frame (Build_URL ProtocolBlob
                                                                              NoneDomain
                                                                              NoneInt
                                                                              a!7)
                                                                   6)
                                                      a!44)
                                                    (TupleOrigin ProtocolHTTP
                                                                 (SomeDomain (subdomain 21
                                                                                        22))
                                                                 (SomeInt 48))
                                                    (SomeCSP (Build_CSP a!9
                                                                        a!10))))
                                 (a!119 (Build_Document 18909
                                                        18910
                                                        (Build_ResponseHeaders
                                                          NoneContentType
                                                          NoneSetCookie
                                                          NoneOrigin
                                                          NoneURL
                                                          NoneCSP
                                                          NoneReferrerPolicy)
                                                        (Build_HTML 18905
                                                                    18906
                                                                    (Build_ArrayoptionHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement
                                                                      NoneHTMLElement))
                                                        (Build_DOM 18907
                                                                   18908
                                                                   (Build_ArrayoptionDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     NoneDOMElement
                                                                     (SomeDOMElement a!114)
                                                                     a!116
                                                                     (SomeDOMElement a!117)
                                                                     (SomeDOMElement a!118)
                                                                     NoneDOMElement))
                                                        (Build_Initiators (SomeInt 52895)
                                                                          (Build_ArrayoptionInt
                                                                            (SomeInt 52167)
                                                                            (SomeInt 63791)
                                                                            (SomeInt 61892)
                                                                            (SomeInt 24459)
                                                                            (SomeInt 46600)
                                                                            (SomeInt 23341)
                                                                            (SomeInt 24506)
                                                                            (SomeInt 40259)))))
                                 (a!146 (Build_Global a!134
                                                      a!135
                                                      (Build_ArrayInt 18913
                                                                      18914
                                                                      18915
                                                                      18916
                                                                      18917
                                                                      18918
                                                                      18919
                                                                      18920)
                                                      (Build_ArrayEmitter
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient
                                                        EmitterClient)
                                                      a!144
                                                      a!145
                                                      (Build_ArrayprodOriginoptionCSP
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 29442)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 37429)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 66629)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 63033)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 22854)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 22247)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 65651)
                                                          NoneCSP)
                                                        (pairOriginoptionCSP
                                                          (OpaqueOrigin 61324)
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
                           (let ((a!51 (Build_ArrayResponse
                                         (Build_Response a!1
                                                         ResponseOk
                                                         a!11
                                                         (SomeContentElement
                                                           (ContentElementHTML
                                                             a!16)))
                                         a!27
                                         a!30
                                         a!34
                                         (Build_Response (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 59313)
                                                                    (url_path_data 60411
                                                                                   60412))
                                                         ResponseOk
                                                         a!35
                                                         a!36)
                                         (Build_Response (Build_URL ProtocolBlob
                                                                    NoneDomain
                                                                    NoneInt
                                                                    a!7)
                                                         ResponseOk
                                                         a!37
                                                         a!45)
                                         (Build_Response (Build_URL ProtocolHTTP
                                                                    NoneDomain
                                                                    (SomeInt 66975)
                                                                    (url_path_data 24855
                                                                                   24856))
                                                         ResponseOk
                                                         a!46
                                                         a!47)
                                         a!50))
                                 (a!63 (Build_Document 17
                                                       1
                                                       a!11
                                                       (Build_HTML 54 55 a!59)
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    (SomeDOMElement a!60)
                                                                    a!61
                                                                    (SomeDOMElement a!54)
                                                                    (SomeDOMElement a!55)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!56)
                                                                    NoneDOMElement))
                                                       a!62))
                                 (a!65 (Build_Document 6
                                                       1
                                                       a!11
                                                       a!16
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!64
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!54)
                                                                    (SomeDOMElement a!55)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!56)
                                                                    NoneDOMElement))
                                                       a!57))
                                 (a!75 (Build_Document 12
                                                       1
                                                       a!11
                                                       a!16
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!74
                                                                    a!61
                                                                    (SomeDOMElement a!54)
                                                                    (SomeDOMElement a!55)
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!56)
                                                                    NoneDOMElement))
                                                       a!57))
                                 (a!94 (consEvent a!93
                                                  (consEvent (EvRequest EmitterClient
                                                                        (Build_Request MethodGet
                                                                                       a!1
                                                                                       a!2
                                                                                       NoneInt)
                                                                        1)
                                                             nilEvent)))
                                 (a!107 (Build_FetchEngine
                                          16
                                          EmitterClient
                                          (Build_Request MethodGet
                                                         (Build_URL ProtocolBlob
                                                                    NoneDomain
                                                                    NoneInt
                                                                    a!7)
                                                         a!2
                                                         NoneInt)
                                          5
                                          (SomeResponse (Build_Response (Build_URL ProtocolBlob
                                                                                   NoneDomain
                                                                                   NoneInt
                                                                                   a!7)
                                                                        ResponseOk
                                                                        a!37
                                                                        a!45))
                                          a!106))
                                 (a!110 (Build_ArrayoptionBlob
                                          NoneBlob
                                          NoneBlob
                                          (SomeBlob a!109)
                                          NoneBlob
                                          NoneBlob
                                          NoneBlob
                                          NoneBlob
                                          NoneBlob))
                                 (a!120 (Build_Window 18911
                                                      (SomeInt 60473)
                                                      (Build_URL ProtocolHTTP
                                                                 NoneDomain
                                                                 (SomeInt 40268)
                                                                 (url_path_data 26211
                                                                                26212))
                                                      NoneDomain
                                                      a!119))
                                 (a!147 (ite (= (frame_window a!132) 5)
                                             (@5ArrayWindow (windows a!146))
                                             (ite (= (frame_window a!132) 6)
                                                  (@6ArrayWindow (windows a!146))
                                                  (@defaultArrayWindow
                                                    (windows a!146))))))
                           (let ((a!89 (Build_ArrayWindow
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!58)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!63)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!65)
                                         (Build_Window 12765
                                                       (SomeInt 43668)
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 62147)
                                                                  (url_path_data 52986
                                                                                 52987))
                                                       NoneDomain
                                                       a!73)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!1
                                                       NoneDomain
                                                       a!75)
                                         (Build_Window 2
                                                       (SomeInt 2)
                                                       a!3
                                                       NoneDomain
                                                       a!83)
                                         (Build_Window 5
                                                       (SomeInt 1)
                                                       (Build_URL ProtocolBlob
                                                                  NoneDomain
                                                                  NoneInt
                                                                  a!7)
                                                       NoneDomain
                                                       a!87)
                                         (Build_Window 2
                                                       (SomeInt 2)
                                                       a!3
                                                       NoneDomain
                                                       a!88)))
                                 (a!95 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!3
                                                                            a!2
                                                                            NoneInt)
                                                             2)
                                                  (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                                   DOMTopLevel))
                                                             a!94)))
                                 (a!111 (Build_State 17
                                                     a!107
                                                     a!108
                                                     (Build_Window 1
                                                                   NoneInt
                                                                   a!1
                                                                   NoneDomain
                                                                   a!63)
                                                     (Build_ArrayoptionSetCookie
                                                       NoneSetCookie
                                                       a!31
                                                       NoneSetCookie
                                                       NoneSetCookie
                                                       NoneSetCookie
                                                       NoneSetCookie
                                                       NoneSetCookie
                                                       NoneSetCookie)
                                                     a!110
                                                     (Build_ArrayoptionStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem
                                                       NoneStorageItem)))
                                 (a!112 (= (Build_Window 1
                                                         NoneInt
                                                         a!1
                                                         NoneDomain
                                                         a!63)
                                           (Build_Window 1
                                                         NoneInt
                                                         a!1
                                                         NoneDomain
                                                         a!63)))
                                 (a!121 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!122 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!123 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!124 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!125 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!126 (@5ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!127 (@6ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!128 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document a!120)))))
                                 (a!148 (ite (= (frame_window a!132) 3)
                                             (@3ArrayWindow (windows a!146))
                                             (ite (= (frame_window a!132) 4)
                                                  (@4ArrayWindow (windows a!146))
                                                  a!147)))
                                 (a!152 (dm_body (dc_dom (wd_document (Build_Window 1
                                                                                    NoneInt
                                                                                    a!1
                                                                                    NoneDomain
                                                                                    a!63)))))
                                 (a!166 (in_body (dc_init (wd_document (Build_Window 1
                                                                                     NoneInt
                                                                                     a!1
                                                                                     NoneDomain
                                                                                     a!63))))))
                           (let ((a!92 (Build_Global a!8
                                                     a!51
                                                     (Build_ArrayInt 0
                                                                     1
                                                                     2
                                                                     3
                                                                     12755
                                                                     12756
                                                                     12757
                                                                     12758)
                                                     (Build_ArrayEmitter
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       a!52
                                                       a!53)
                                                     a!89
                                                     a!90
                                                     (Build_ArrayprodOriginoptionCSP
                                                       a!91
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 43089)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 19708)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 47550)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 23675)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 66757)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 44276)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 62734)
                                                         NoneCSP))
                                                     (Build_Config false
                                                                   false
                                                                   false
                                                                   false
                                                                   true
                                                                   false
                                                                   false
                                                                   false
                                                                   true
                                                                   true
                                                                   false
                                                                   false)))
                                 (a!96 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                        (DOMIndex 0)))
                                                  (consEvent (EvResponse a!27 2)
                                                             a!95)))
                                 (a!129 (ite (= 4 4)
                                             a!125
                                             (ite (= 4 5)
                                                  a!126
                                                  (ite (= 4 6) a!127 a!128))))
                                 (a!149 (ite (= (frame_window a!132) 1)
                                             (@1ArrayWindow (windows a!146))
                                             (ite (= (frame_window a!132) 2)
                                                  (@2ArrayWindow (windows a!146))
                                                  a!148)))
                                 (a!153 (ite (= 0 4)
                                             (@4ArrayoptionDOMElement a!152)
                                             (ite (= 0 5)
                                                  (@5ArrayoptionDOMElement
                                                    a!152)
                                                  (ite (= 0 6)
                                                       (@6ArrayoptionDOMElement
                                                         a!152)
                                                       (@defaultArrayoptionDOMElement
                                                         a!152)))))
                                 (a!167 (ite (= 0 4)
                                             (@4ArrayoptionInt a!166)
                                             (ite (= 0 5)
                                                  (@5ArrayoptionInt a!166)
                                                  (ite (= 0 6)
                                                       (@6ArrayoptionInt a!166)
                                                       (@defaultArrayoptionInt
                                                         a!166))))))
                           (let ((a!97 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!4
                                                                            (Build_RequestHeaders
                                                                              NoneOrigin
                                                                              a!5
                                                                              NoneURL)
                                                                            NoneInt)
                                                             3)
                                                  a!96))
                                 (a!113 (and a!112
                                             a!112
                                             (= (st_window a!111)
                                                (Build_Window 1
                                                              NoneInt
                                                              a!1
                                                              NoneDomain
                                                              a!63))
                                             (= (DOMPath nilInt (DOMIndex 0))
                                                (DOMPath nilInt (DOMIndex 0)))
                                             (= (DOMPath nilInt (DOMIndex 0))
                                                (DOMPath nilInt (DOMIndex 0)))
                                             (= a!92 a!92)))
                                 (a!130 (ite (= 4 1)
                                             a!122
                                             (ite (= 4 2)
                                                  a!123
                                                  (ite (= 4 3) a!124 a!129))))
                                 (a!150 (= (ite (= (frame_window a!132) 0)
                                                (@0ArrayWindow (windows a!146))
                                                a!149)
                                           H))
                                 (a!154 (ite (= 0 1)
                                             (@1ArrayoptionDOMElement a!152)
                                             (ite (= 0 2)
                                                  (@2ArrayoptionDOMElement
                                                    a!152)
                                                  (ite (= 0 3)
                                                       (@3ArrayoptionDOMElement
                                                         a!152)
                                                       a!153))))
                                 (a!168 (ite (= 0 1)
                                             (@1ArrayoptionInt a!166)
                                             (ite (= 0 2)
                                                  (@2ArrayoptionInt a!166)
                                                  (ite (= 0 3)
                                                       (@3ArrayoptionInt a!166)
                                                       a!167)))))
                           (let ((a!98 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                                 nilInt)
                                                                        (DOMIndex 1)))
                                                  (consEvent (EvResponse a!30 3)
                                                             a!97)))
                                 (a!131 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= 4 0)
                                                                 a!121
                                                                 a!130))))
                                 (a!133 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= 4 0)
                                                                 a!121
                                                                 a!130))))
                                 (a!155 (@1DOMElementResource
                                          (@0SomeDOMElement (ite (= 0 0)
                                                                 (@0ArrayoptionDOMElement
                                                                   a!152)
                                                                 a!154))))
                                 (a!156 ((_ is DOMElementForm)
                                          (@0SomeDOMElement (ite (= 0 0)
                                                                 (@0ArrayoptionDOMElement
                                                                   a!152)
                                                                 a!154))))
                                 (a!169 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           0))
                                 (a!170 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           1))
                                 (a!171 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           2))
                                 (a!172 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           3))
                                 (a!173 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           4))
                                 (a!174 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           5))
                                 (a!175 (= (@0SomeInt (ite (= 0 0)
                                                           (@0ArrayoptionInt a!166)
                                                           a!168))
                                           6)))
                           (let ((a!99 (consEvent (EvResponse a!34 4)
                                                  (consEvent (EvRequest EmitterClient
                                                                        (Build_Request MethodGet
                                                                                       a!6
                                                                                       a!2
                                                                                       NoneInt)
                                                                        4)
                                                             a!98)))
                                 (a!151 (and (= (@0ContentElementFrame a!131)
                                                a!132)
                                             (= (@1ContentElementFrame a!131) D)
                                             (not ((_ is ContentElementScript)
                                                    a!131))
                                             (not ((_ is ContentElementImage)
                                                    a!131))
                                             (not ((_ is ContentElementHTML)
                                                    a!131))
                                             (not a!133)
                                             ((_ is SomeDOMElement)
                                               (ite (= 4 0) a!121 a!130))
                                             (= H O)
                                             (= N O)
                                             (= I N)
                                             (= (Build_Window 1
                                                              NoneInt
                                                              a!1
                                                              NoneDomain
                                                              a!63)
                                                I)
                                             a!150
                                             (= (st_window a!111) a!120)
                                             (= L (DOMPath nilInt DOMTopLevel))
                                             (= L (DOMPath nilInt DOMTopLevel))
                                             (= A
                                                (DOMPath (consInt 4 nilInt)
                                                         DOMTopLevel))
                                             (= (DOMPath nilInt (DOMIndex 0)) A)
                                             (= a!92 a!146)
                                             (= a!146 K)))
                                 (a!157 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                6)
                                             (@6ArrayWindow (windows a!92))
                                             (@defaultArrayWindow
                                               (windows a!92))))
                                 (a!176 (ite a!174
                                             (@5ArrayWindow (windows a!92))
                                             (ite a!175
                                                  (@6ArrayWindow (windows a!92))
                                                  (@defaultArrayWindow
                                                    (windows a!92))))))
                           (let ((a!100 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                         (DOMIndex 1)))
                                                   a!99))
                                 (a!158 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                5)
                                             (@5ArrayWindow (windows a!92))
                                             a!157))
                                 (a!177 (ite a!172
                                             (@3ArrayWindow (windows a!92))
                                             (ite a!173
                                                  (@4ArrayWindow (windows a!92))
                                                  a!176))))
                           (let ((a!101 (consEvent (EvScriptCreateBlobUrl
                                                     (DOMPath nilInt
                                                              (DOMIndex 1))
                                                     (Build_URL ProtocolBlob
                                                                NoneDomain
                                                                NoneInt
                                                                a!7))
                                                   a!100))
                                 (a!159 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                4)
                                             (@4ArrayWindow (windows a!92))
                                             a!158))
                                 (a!178 (ite a!170
                                             (@1ArrayWindow (windows a!92))
                                             (ite a!171
                                                  (@2ArrayWindow (windows a!92))
                                                  a!177))))
                           (let ((a!102 (consEvent (EvScriptNavigateFrame
                                                     (DOMPath (consInt 0 nilInt)
                                                              (DOMIndex 1))
                                                     (DOMPath nilInt
                                                              (DOMIndex 0))
                                                     (Build_Frame a!3 5)
                                                     (Build_URL ProtocolBlob
                                                                NoneDomain
                                                                NoneInt
                                                                a!7))
                                                   a!101))
                                 (a!160 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                3)
                                             (@3ArrayWindow (windows a!92))
                                             a!159))
                                 (a!179 (wd_document (ite a!169
                                                          (@0ArrayWindow (windows a!92))
                                                          a!178))))
                           (let ((a!103 (consEvent (EvRequest EmitterClient
                                                              (Build_Request MethodGet
                                                                             (Build_URL ProtocolBlob
                                                                                        NoneDomain
                                                                                        NoneInt
                                                                                        a!7)
                                                                             a!2
                                                                             NoneInt)
                                                              5)
                                                   a!102))
                                 (a!161 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                2)
                                             (@2ArrayWindow (windows a!92))
                                             a!160)))
                           (let ((a!104 (consEvent (EvResponse (Build_Response (Build_URL ProtocolBlob
                                                                                          NoneDomain
                                                                                          NoneInt
                                                                                          a!7)
                                                                               ResponseOk
                                                                               a!37
                                                                               a!45)
                                                               5)
                                                   a!103))
                                 (a!162 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                1)
                                             (@1ArrayWindow (windows a!92))
                                             a!161)))
                           (let ((a!105 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                         (DOMIndex 0)))
                                                   a!104))
                                 (a!163 (ite (= (frame_window (@0ContentElementFrame
                                                                a!155))
                                                0)
                                             (@0ArrayWindow (windows a!92))
                                             a!162)))
                           (let ((a!164 (not ((_ is ProtocolHTTPS)
                                               (url_protocol (wd_location a!163)))))
                                 (a!165 (not ((_ is ProtocolHTTP)
                                               (url_protocol (wd_location a!163)))))
                                 (a!180 (= (rp_hd_csp (dc_headers (wd_document a!163)))
                                           (rp_hd_csp (dc_headers a!179)))))
                           (let ((a!181 (and (Reachable a!92 a!105 a!111)
                                             (= a!105 a!105)
                                             (or a!113 a!151)
                                             (c_csp_inherit_local_from_initiator
                                               (config a!92))
                                             (c_csp_inherit_blob_from_creator
                                               (config a!92))
                                             (not ((_ is ContentElementScript)
                                                    a!155))
                                             (not ((_ is ContentElementImage)
                                                    a!155))
                                             (not ((_ is ContentElementHTML)
                                                    a!155))
                                             (not a!156)
                                             ((_ is SomeDOMElement)
                                               (ite (= 0 0)
                                                    (@0ArrayoptionDOMElement
                                                      a!152)
                                                    a!154))
                                             a!164
                                             a!165
                                             ((_ is SomeInt)
                                               (ite (= 0 0)
                                                    (@0ArrayoptionInt a!166)
                                                    a!168))
                                             (not a!180)
                                             (= a!105 a!105))))
                             (=> a!181 (query!0 a!111 a!105 a!92)))))))))))))))))))
                           :weight 0))))
      (a!11 (Build_ArrayRequest
              (Build_Request MethodGet a!4 a!5 NoneInt)
              (Build_Request MethodGet a!6 a!5 NoneInt)
              (Build_Request MethodGet
                             a!7
                             (Build_RequestHeaders NoneOrigin a!8 NoneURL)
                             NoneInt)
              (Build_Request MethodGet a!9 a!5 NoneInt)
              (Build_Request MethodGet
                             (Build_URL ProtocolBlob
                                        NoneDomain
                                        (SomeInt 20463)
                                        (url_path_data 2552 19503))
                             a!5
                             (SomeInt 24537))
              (Build_Request MethodGet
                             (Build_URL ProtocolHTTP
                                        NoneDomain
                                        (SomeInt 63108)
                                        (url_path_data 64564 64565))
                             a!5
                             (SomeInt 35099))
              (Build_Request MethodGet
                             (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
                             a!5
                             NoneInt)
              (Build_Request MethodGet
                             (Build_URL ProtocolHTTP
                                        NoneDomain
                                        (SomeInt 23392)
                                        (url_path_res slash))
                             a!5
                             (SomeInt 58160))))
      (a!14 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 50)
                                  (url_path_data 51 52)))
              (SomeCSP (Build_CSP a!12 a!13))
              NoneReferrerPolicy))
      (a!19 (Build_HTML 54
                        55
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!6))
                          (SomeHTMLElement (HTMLScript a!9))
                          a!15
                          a!16
                          a!17
                          NoneHTMLElement
                          a!18
                          NoneHTMLElement)))
      (a!21 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              (SomeSetCookie (Build_SetCookie (NoPrefix 70)
                                              75
                                              NoneDomain
                                              (subdomain 21 22)
                                              (anypath 72)
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 102))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 103)
                                  (url_path_data 104 105)))
              (SomeCSP a!20)
              NoneReferrerPolicy))
      (a!29 (Build_HTML 107
                        108
                        (Build_ArrayoptionHTMLElement
                          a!22
                          (SomeHTMLElement (HTMLScript a!7))
                          a!23
                          a!24
                          a!25
                          a!26
                          a!27
                          a!28)))
      (a!32 (Build_ResponseHeaders
              (SomeContentType ContentTypeScript)
              NoneSetCookie
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 97)
                                  (url_path_data 98 99)))
              (SomeCSP a!31)
              NoneReferrerPolicy))
      (a!36 (Build_ResponseHeaders
              (SomeContentType ContentTypeScript)
              a!34
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 92)
                                  (url_path_data 93 94)))
              (SomeCSP a!35)
              NoneReferrerPolicy))
      (a!40 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              NoneOrigin
              NoneURL
              (SomeCSP (Build_CSP a!12 a!13))
              NoneReferrerPolicy))
      (a!47 (Build_HTML 12766
                        12767
                        (Build_ArrayoptionHTMLElement
                          NoneHTMLElement
                          a!41
                          a!42
                          a!43
                          a!44
                          NoneHTMLElement
                          a!45
                          a!46)))
      (a!53 (Build_Response (Build_URL ProtocolHTTP
                                       (SomeDomain (domain 69452))
                                       (SomeInt 35652)
                                       (url_path_data 46047 46048))
                            ResponseOk
                            a!51
                            a!52))
      (a!62 (Build_ArrayoptionHTMLElement
              (SomeHTMLElement (HTMLFrame (Build_URL ProtocolBlob
                                                     NoneDomain
                                                     NoneInt
                                                     a!10)))
              (SomeHTMLElement (HTMLScript a!9))
              a!15
              a!16
              a!17
              NoneHTMLElement
              a!18
              NoneHTMLElement))
      (a!64 (SomeDOMElement (DOMElementResource
                              a!9
                              (ContentElementScript (Build_Script a!9 11)))))
      (a!76 (Build_Document 12763
                            12764
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 12759
                                        12760
                                        (Build_ArrayoptionHTMLElement
                                          a!69
                                          a!70
                                          a!71
                                          a!72
                                          a!73
                                          NoneHTMLElement
                                          a!74
                                          a!75))
                            (Build_DOM 12761
                                       12762
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 36476)
                                              (Build_ArrayoptionInt
                                                (SomeInt 29506)
                                                (SomeInt 24857)
                                                (SomeInt 51228)
                                                (SomeInt 62306)
                                                (SomeInt 19925)
                                                (SomeInt 29652)
                                                (SomeInt 64751)
                                                (SomeInt 52029)))))
      (a!80 (SomeDOMElement (DOMElementResource
                              a!7
                              (ContentElementScript (Build_Script a!7 8))))))
(let ((a!30 (Build_Response a!6
                            ResponseOk
                            a!21
                            (SomeContentElement
                              (ContentElementFrame (Build_Frame a!6 106) a!29))))
      (a!33 (Build_Response a!7
                            ResponseOk
                            a!32
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!7 8)))))
      (a!37 (Build_Response a!9
                            ResponseOk
                            a!36
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!9 11)))))
      (a!48 (SomeContentElement
              (ContentElementFrame
                (Build_Frame (Build_URL ProtocolBlob NoneDomain NoneInt a!10) 6)
                a!47)))
      (a!61 (Build_Document 3
                            1
                            a!14
                            a!19
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!57)
                                         (SomeDOMElement a!58)
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!59)
                                         NoneDOMElement))
                            a!60))
      (a!63 (DOMElementResource
              (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
              (ContentElementFrame
                (Build_Frame (Build_URL ProtocolBlob NoneDomain NoneInt a!10) 6)
                a!47)))
      (a!67 (SomeDOMElement (DOMElementResource
                              a!6
                              (ContentElementFrame (Build_Frame a!6 106) a!29))))
      (a!77 (SomeDOMElement (DOMElementResource
                              a!7
                              (ContentElementFrame (Build_Frame a!6 5) a!29))))
      (a!86 (Build_Document 9
                            2
                            a!21
                            a!29
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!79)
                                         a!80
                                         (SomeDOMElement a!81)
                                         (SomeDOMElement a!82)
                                         (SomeDOMElement a!83)
                                         NoneDOMElement
                                         (SomeDOMElement a!84)
                                         (SomeDOMElement a!85)))
                            a!60))
      (a!90 (Build_Document 17
                            5
                            a!40
                            a!47
                            (Build_DOM 5
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!87)
                                         (SomeDOMElement a!88)
                                         (SomeDOMElement a!89)
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            a!60))
      (a!91 (Build_Document 6
                            2
                            a!21
                            a!29
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!79)
                                         NoneDOMElement
                                         (SomeDOMElement a!81)
                                         (SomeDOMElement a!82)
                                         (SomeDOMElement a!83)
                                         NoneDOMElement
                                         (SomeDOMElement a!84)
                                         (SomeDOMElement a!85)))
                            a!60))
      (a!96 (EvResponse (Build_Response a!4
                                        ResponseOk
                                        a!14
                                        (SomeContentElement
                                          (ContentElementHTML a!19)))
                        1))
      (a!111 (Build_Document 14
                             1
                             a!14
                             (Build_HTML 54 55 a!62)
                             (Build_DOM 1
                                        0
                                        (Build_ArrayoptionDOMElement
                                          NoneDOMElement
                                          a!64
                                          (SomeDOMElement a!57)
                                          (SomeDOMElement a!58)
                                          NoneDOMElement
                                          NoneDOMElement
                                          (SomeDOMElement a!59)
                                          NoneDOMElement))
                             a!65))
      (a!112 (Build_Blob (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
                         (ContentElementFrame
                           (Build_Frame (Build_URL ProtocolBlob
                                                   NoneDomain
                                                   NoneInt
                                                   a!10)
                                        6)
                           a!47)
                         (TupleOrigin ProtocolHTTP
                                      (SomeDomain (subdomain 21 22))
                                      (SomeInt 48))
                         (SomeCSP (Build_CSP a!12 a!13)))))
(let ((a!54 (Build_ArrayResponse
              (Build_Response a!4
                              ResponseOk
                              a!14
                              (SomeContentElement (ContentElementHTML a!19)))
              a!30
              a!33
              a!37
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 59313)
                                         (url_path_data 60411 60412))
                              ResponseOk
                              a!38
                              a!39)
              (Build_Response (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
                              ResponseOk
                              a!40
                              a!48)
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 66975)
                                         (url_path_data 24855 24856))
                              ResponseOk
                              a!49
                              a!50)
              a!53))
      (a!66 (Build_Document 17
                            1
                            a!14
                            (Build_HTML 54 55 a!62)
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!63)
                                         a!64
                                         (SomeDOMElement a!57)
                                         (SomeDOMElement a!58)
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!59)
                                         NoneDOMElement))
                            a!65))
      (a!68 (Build_Document 6
                            1
                            a!14
                            a!19
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!67
                                         NoneDOMElement
                                         (SomeDOMElement a!57)
                                         (SomeDOMElement a!58)
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!59)
                                         NoneDOMElement))
                            a!60))
      (a!78 (Build_Document 12
                            1
                            a!14
                            a!19
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!77
                                         a!64
                                         (SomeDOMElement a!57)
                                         (SomeDOMElement a!58)
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!59)
                                         NoneDOMElement))
                            a!60))
      (a!97 (consEvent a!96
                       (consEvent (EvRequest EmitterClient
                                             (Build_Request MethodGet
                                                            a!4
                                                            a!5
                                                            NoneInt)
                                             1)
                                  nilEvent)))
      (a!109 (Build_FetchEngine
               16
               EmitterClient
               (Build_Request MethodGet
                              (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
                              a!5
                              NoneInt)
               5
               (SomeResponse (Build_Response (Build_URL ProtocolBlob
                                                        NoneDomain
                                                        NoneInt
                                                        a!10)
                                             ResponseOk
                                             a!40
                                             a!48))
               a!108))
      (a!113 (Build_ArrayoptionBlob
               NoneBlob
               NoneBlob
               (SomeBlob a!112)
               NoneBlob
               NoneBlob
               NoneBlob
               NoneBlob
               NoneBlob))
      (a!121 (Build_FetchEngine
               11
               EmitterClient
               (Build_Request MethodGet a!9 a!5 NoneInt)
               4
               (SomeResponse a!37)
               a!118)))
(let ((a!92 (Build_ArrayWindow
              (Build_Window 1 NoneInt a!4 NoneDomain a!61)
              (Build_Window 1 NoneInt a!4 NoneDomain a!66)
              (Build_Window 1 NoneInt a!4 NoneDomain a!68)
              (Build_Window 12765
                            (SomeInt 43668)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 62147)
                                       (url_path_data 52986 52987))
                            NoneDomain
                            a!76)
              (Build_Window 1 NoneInt a!4 NoneDomain a!78)
              (Build_Window 2 (SomeInt 2) a!6 NoneDomain a!86)
              (Build_Window 5
                            (SomeInt 1)
                            (Build_URL ProtocolBlob NoneDomain NoneInt a!10)
                            NoneDomain
                            a!90)
              (Build_Window 2 (SomeInt 2) a!6 NoneDomain a!91)))
      (a!98 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet a!6 a!5 NoneInt)
                                  2)
                       (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                  a!97)))
      (a!114 (Build_State 17
                          a!109
                          a!110
                          (Build_Window 1 NoneInt a!4 NoneDomain a!66)
                          (Build_ArrayoptionSetCookie
                            NoneSetCookie
                            a!34
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie)
                          a!113
                          (Build_ArrayoptionStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem)))
      (a!119 (Build_State 15
                          (Build_FetchEngine
                            15
                            EmitterClient
                            (Build_Request MethodGet
                                           (Build_URL ProtocolBlob
                                                      NoneDomain
                                                      NoneInt
                                                      a!10)
                                           a!5
                                           NoneInt)
                            5
                            NoneResponse
                            a!118)
                          a!110
                          (Build_Window 1 NoneInt a!4 NoneDomain a!111)
                          (Build_ArrayoptionSetCookie
                            NoneSetCookie
                            a!34
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie
                            NoneSetCookie)
                          a!113
                          (Build_ArrayoptionStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem)))
      (a!127 (Build_State 12
                          a!121
                          a!110
                          (Build_Window 1 NoneInt a!4 NoneDomain a!78)
                          (Build_ArrayoptionSetCookie
                            NoneSetCookie
                            a!34
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
                            NoneBlob
                            NoneBlob
                            NoneBlob)
                          (Build_ArrayoptionStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem
                            NoneStorageItem))))
(let ((a!95 (Build_Global a!11
                          a!54
                          (Build_ArrayInt 0 1 2 3 12755 12756 12757 12758)
                          (Build_ArrayEmitter
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            a!55
                            a!56)
                          a!92
                          a!93
                          (Build_ArrayprodOriginoptionCSP
                            a!94
                            (pairOriginoptionCSP (OpaqueOrigin 43089) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 19708) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 47550) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 23675) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 66757) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 44276) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 62734) NoneCSP))
                          (Build_Config false
                                        false
                                        false
                                        false
                                        true
                                        false
                                        false
                                        false
                                        true
                                        true
                                        false
                                        false)))
      (a!99 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 0)))
                       (consEvent (EvResponse a!30 2) a!98))))
(let ((a!100 (consEvent (EvRequest EmitterClient
                                   (Build_Request MethodGet
                                                  a!7
                                                  (Build_RequestHeaders
                                                    NoneOrigin
                                                    a!8
                                                    NoneURL)
                                                  NoneInt)
                                   3)
                        a!99)))
(let ((a!101 (consEvent (EvDOMUpdate (DOMPath (consInt 0 nilInt) (DOMIndex 1)))
                        (consEvent (EvResponse a!33 3) a!100))))
(let ((a!102 (consEvent (EvResponse a!37 4)
                        (consEvent (EvRequest EmitterClient
                                              (Build_Request MethodGet
                                                             a!9
                                                             a!5
                                                             NoneInt)
                                              4)
                                   a!101))))
(let ((a!103 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 1))) a!102)))
(let ((a!104 (consEvent (EvScriptCreateBlobUrl
                          (DOMPath nilInt (DOMIndex 1))
                          (Build_URL ProtocolBlob NoneDomain NoneInt a!10))
                        a!103)))
(let ((a!105 (consEvent (EvScriptNavigateFrame
                          (DOMPath (consInt 0 nilInt) (DOMIndex 1))
                          (DOMPath nilInt (DOMIndex 0))
                          (Build_Frame a!6 5)
                          (Build_URL ProtocolBlob NoneDomain NoneInt a!10))
                        a!104)))
(let ((a!106 (consEvent (EvRequest EmitterClient
                                   (Build_Request MethodGet
                                                  (Build_URL ProtocolBlob
                                                             NoneDomain
                                                             NoneInt
                                                             a!10)
                                                  a!5
                                                  NoneInt)
                                   5)
                        a!105)))
(let ((a!107 (consEvent (EvResponse (Build_Response (Build_URL ProtocolBlob
                                                               NoneDomain
                                                               NoneInt
                                                               a!10)
                                                    ResponseOk
                                                    a!40
                                                    a!48)
                                    5)
                        a!106)))
(let ((a!115 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 0))) a!107)))
(let ((a!116 (=> (Reachable a!95
                            a!107
                            (Build_State 16
                                         a!109
                                         a!110
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!111)
                                         (Build_ArrayoptionSetCookie
                                           NoneSetCookie
                                           a!34
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie)
                                         a!113
                                         (Build_ArrayoptionStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem)))
                 (query!0 a!114 a!115 a!95)))
      (a!122 (=> (Reachable a!95
                            a!105
                            (Build_State 14
                                         a!121
                                         a!110
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!111)
                                         (Build_ArrayoptionSetCookie
                                           NoneSetCookie
                                           a!34
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie)
                                         a!113
                                         (Build_ArrayoptionStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem)))
                 (query!0 a!114 a!115 a!95)))
      (a!125 (=> (Reachable a!95
                            a!104
                            (Build_State 13
                                         a!121
                                         a!110
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!78)
                                         (Build_ArrayoptionSetCookie
                                           NoneSetCookie
                                           a!34
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie
                                           NoneSetCookie)
                                         a!113
                                         (Build_ArrayoptionStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem
                                           NoneStorageItem)))
                 (query!0 a!114 a!115 a!95))))
(let ((a!123 (hyper-res (hyper-res (hyper-res a!2 a!3 a!116)
                                   a!117
                                   (=> (Reachable a!95 a!106 a!119)
                                       (query!0 a!114 a!115 a!95)))
                        a!120
                        a!122)))
  (hyper-res (hyper-res (hyper-res a!123 a!124 a!125)
                        a!126
                        (=> (Reachable a!95 a!103 a!127)
                            (query!0 a!114 a!115 a!95)))
             a!128
             (query!0 a!114 a!115 a!95)))))))))))))))))))
