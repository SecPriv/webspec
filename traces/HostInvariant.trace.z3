
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
                              (Y listEvent)
                              (Z Int)
                              (A1 SetCookie)
                              (B1 Domain)
                              (C1 Response)
                              (D1 Request)
                              (E1 Int)
                              (F1 Response)
                              (G1 Request)
                              (H1 Int)
                              (I1 Response)
                              (J1 Request)
                              (K1 Int)
                              (L1 Response)
                              (M1 Request)
                              (N1 Int)
                              (O1 listEvent)
                              (P1 State))
                       (! (let ((a!1 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      DOMTopLevel))
                                                (consEvent (EvResponse L1 N1)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 M1
                                                                                 N1)
                                                                      nilEvent))))
                                (a!8 (consEvent (EvScriptSetCookie
                                                  (DOMPath V (DOMIndex W))
                                                  (DOMPath nilInt DOMTopLevel)
                                                  Z
                                                  A1)
                                                Y))
                                (a!9 (= (sc_reg_domain A1)
                                        (@0SomeDomain (url_host (wd_location X)))))
                                (a!10 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!11 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!12 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!13 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!14 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!15 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document X)))))
                                (a!20 (and (= T U)
                                           (= X T)
                                           (= (st_window P1) U)
                                           (= R (DOMPath nilInt S))
                                           (= (DOMPath V (DOMIndex W)) R)
                                           (= P Q)))
                                (a!21 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!22 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!23 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!24 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!25 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!26 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C)))))
                                (a!34 (ite (= (frame_window E) 3)
                                           (@3ArrayWindow (windows J))
                                           (ite (= (frame_window E) 4)
                                                (@4ArrayWindow (windows J))
                                                (@defaultArrayWindow
                                                  (windows J))))))
                          (let ((a!2 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      (DOMIndex 0)))
                                                (consEvent (EvResponse I1 K1)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 J1
                                                                                 K1)
                                                                      a!1))))
                                (a!16 (ite (= W 2)
                                           a!12
                                           (ite (= W 3)
                                                a!13
                                                (ite (= W 4) a!14 a!15))))
                                (a!27 (ite (= B 2)
                                           a!23
                                           (ite (= B 3)
                                                a!24
                                                (ite (= B 4) a!25 a!26))))
                                (a!35 (ite (= (frame_window E) 1)
                                           (@1ArrayWindow (windows J))
                                           (ite (= (frame_window E) 2)
                                                (@2ArrayWindow (windows J))
                                                a!34))))
                          (let ((a!3 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      (DOMIndex 1)))
                                                (consEvent (EvResponse F1 H1)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 G1
                                                                                 H1)
                                                                      a!2))))
                                (a!17 (ite (= W 0) a!10 (ite (= W 1) a!11 a!16)))
                                (a!28 (ite (= B 0) a!21 (ite (= B 1) a!22 a!27)))
                                (a!36 (= (ite (= (frame_window E) 0)
                                              (@0ArrayWindow (windows J))
                                              a!35)
                                         H)))
                          (let ((a!4 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                               nilInt)
                                                                      (DOMIndex 0)))
                                                (consEvent (EvResponse C1 E1)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 D1
                                                                                 E1)
                                                                      a!3))))
                                (a!18 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!17)))))
                                (a!19 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!17)))))
                                (a!29 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!28)))
                                         E))
                                (a!30 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!28)))
                                         D))
                                (a!31 (not ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!28)))))
                                (a!32 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!28)))))
                                (a!33 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!28))))))
                          (let ((a!5 (consEvent (EvScriptDomainRelaxation
                                                  (DOMPath nilInt (DOMIndex 1))
                                                  B1)
                                                a!4))
                                (a!37 (and a!29
                                           a!30
                                           a!31
                                           a!32
                                           a!33
                                           (not ((_ is DOMElementForm)
                                                  (@0SomeDOMElement a!28)))
                                           ((_ is SomeDOMElement) a!28)
                                           (= N O)
                                           (= X I)
                                           (= I N)
                                           (= H O)
                                           a!36
                                           (= (st_window P1) C)
                                           (= L (DOMPath F G))
                                           (= L (DOMPath nilInt M))
                                           (= A (DOMPath (consInt B F) G))
                                           (= (DOMPath V (DOMIndex W)) A)
                                           (= P J)
                                           (= J K))))
                          (let ((a!6 (consEvent (EvScriptDomainRelaxation
                                                  (DOMPath (consInt 0 nilInt)
                                                           (DOMIndex 0))
                                                  B1)
                                                a!5)))
                          (let ((a!7 (consEvent (EvScriptSetCookie
                                                  (DOMPath (consInt 0 nilInt)
                                                           (DOMIndex 0))
                                                  (DOMPath nilInt DOMTopLevel)
                                                  Z
                                                  A1)
                                                a!6)))
                          (let ((a!38 (and (Reachable P O1 P1)
                                           (= O1 a!7)
                                           (= O1 a!8)
                                           (not a!9)
                                           ((_ is SomeDomain)
                                             (url_host (wd_location X)))
                                           ((_ is SomeDOMElement) a!17)
                                           (not ((_ is DOMElementForm)
                                                  (@0SomeDOMElement a!17)))
                                           a!18
                                           a!19
                                           ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!17)))
                                           (or a!20 a!37)
                                           ((_ is Host) (sc_name A1)))))
                            (=> a!38 (query!0 P1 O1 P))))))))))
                          :weight 0))))
      (a!3 (asserted (forall ((A State)
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
                              (E1 NestedDOMPath)
                              (F1 Int)
                              (G1 Window)
                              (H1 HTML)
                              (I1 Frame)
                              (J1 listInt)
                              (K1 DOMSelector)
                              (L1 Window)
                              (M1 SetCookie)
                              (N1 Window)
                              (O1 Int)
                              (P1 Int)
                              (Q1 Global)
                              (R1 Global)
                              (S1 NestedDOMPath)
                              (T1 Window)
                              (U1 SetCookie)
                              (V1 Window)
                              (W1 Int)
                              (X1 Global)
                              (Y1 NestedDOMPath)
                              (Z1 Window)
                              (A2 SetCookie)
                              (B2 Window)
                              (C2 ArrayoptionSetCookie)
                              (D2 ArrayoptionSetCookie)
                              (E2 NestedDOMPath)
                              (F2 Int)
                              (G2 SetCookie)
                              (H2 listEvent)
                              (I2 Int)
                              (J2 FetchEngine)
                              (K2 ServiceWorker)
                              (L2 ArrayoptionSetCookie)
                              (M2 ArrayoptionBlob)
                              (N2 ArrayoptionStorageItem))
                       (! (let ((a!1 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                          C2)))
                                        (sc_reg_domain G2)))
                                (a!2 (= (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                    C2)))
                                        (sc_path G2)))
                                (a!3 (= (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                    C2)))
                                        (sc_name G2)))
                                (a!5 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                          C2)))
                                        (sc_reg_domain G2)))
                                (a!6 (= (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                    C2)))
                                        (sc_path G2)))
                                (a!7 (= (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                    C2)))
                                        (sc_name G2)))
                                (a!9 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                          C2)))
                                        (sc_reg_domain G2)))
                                (a!10 (= (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_path G2)))
                                (a!11 (= (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_name G2)))
                                (a!13 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                           C2)))
                                         (sc_reg_domain G2)))
                                (a!14 (= (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_path G2)))
                                (a!15 (= (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_name G2)))
                                (a!17 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                           C2)))
                                         (sc_reg_domain G2)))
                                (a!18 (= (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_path G2)))
                                (a!19 (= (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                     C2)))
                                         (sc_name G2)))
                                (a!21 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                           C2)))
                                         (sc_reg_domain G2)))
                                (a!22 (= (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                     C2)))
                                         (sc_path G2)))
                                (a!23 (= (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                     C2)))
                                         (sc_name G2)))
                                (a!26 (ite (= F2 3)
                                           (Build_ArrayoptionSetCookie
                                             (@0ArrayoptionSetCookie D2)
                                             (@1ArrayoptionSetCookie D2)
                                             (@2ArrayoptionSetCookie D2)
                                             (SomeSetCookie G2)
                                             (@4ArrayoptionSetCookie D2)
                                             (@defaultArrayoptionSetCookie D2))
                                           (ite (= F2 4)
                                                (Build_ArrayoptionSetCookie
                                                  (@0ArrayoptionSetCookie D2)
                                                  (@1ArrayoptionSetCookie D2)
                                                  (@2ArrayoptionSetCookie D2)
                                                  (@3ArrayoptionSetCookie D2)
                                                  (SomeSetCookie G2)
                                                  (@defaultArrayoptionSetCookie
                                                    D2))
                                                D2)))
                                (a!29 (ite (= F2 2)
                                           (@2ArrayoptionSetCookie D2)
                                           (ite (= F2 3)
                                                (@3ArrayoptionSetCookie D2)
                                                (ite (= F2 4)
                                                     (@4ArrayoptionSetCookie D2)
                                                     (@defaultArrayoptionSetCookie
                                                       D2)))))
                                (a!31 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!32 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!33 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!34 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!35 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!36 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                (a!42 (and (sc_secure A2)
                                           (= (url_protocol (wd_location B2))
                                              ProtocolHTTPS)))
                                (a!43 (and ((_ is SomeDomain)
                                             (wd_document_domain B2))
                                           (= (url_protocol (wd_location Z1))
                                              (url_protocol (wd_location B2)))
                                           (= (@0SomeDomain (wd_document_domain
                                                              Z1))
                                              (@0SomeDomain (wd_document_domain
                                                              B2)))))
                                (a!44 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location Z1)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location Z1)))))
                                (a!45 (SomeOrigin (TupleOrigin (url_protocol (wd_location Z1))
                                                               (url_host (wd_location Z1))
                                                               (url_port (wd_location Z1)))))
                                (a!46 (OpaqueOrigin (@0url_path_data (url_path (wd_location Z1)))))
                                (a!48 (SomeOrigin (@0url_path_blob (url_path (wd_location Z1)))))
                                (a!52 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location B2)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location B2)))))
                                (a!53 (SomeOrigin (TupleOrigin (url_protocol (wd_location B2))
                                                               (url_host (wd_location B2))
                                                               (url_port (wd_location B2)))))
                                (a!54 (OpaqueOrigin (@0url_path_data (url_path (wd_location B2)))))
                                (a!56 (SomeOrigin (@0url_path_blob (url_path (wd_location B2)))))
                                (a!61 (or (not (sc_secure A2))
                                          (= (url_protocol (wd_location B2))
                                             ProtocolHTTPS)))
                                (a!62 (@0domain (@0SomeDomain (url_host (wd_location B2)))))
                                (a!64 ((_ is domain)
                                        (@0SomeDomain (url_host (wd_location B2)))))
                                (a!66 (@0subdomain (@0SomeDomain (url_host (wd_location B2)))))
                                (a!68 (@1subdomain (@0SomeDomain (url_host (wd_location B2)))))
                                (a!72 (= (sc_reg_domain A2)
                                         (@0SomeDomain (url_host (wd_location B2)))))
                                (a!75 (not ((_ is url_path_blob)
                                             (url_path (wd_location B2)))))
                                (a!76 (not ((_ is url_path_data)
                                             (url_path (wd_location B2)))))
                                (a!77 (= (@0url_path_res (url_path (wd_location B2)))
                                         slash))
                                (a!81 (and (sc_secure U1)
                                           (= (url_protocol (wd_location V1))
                                              ProtocolHTTPS)))
                                (a!82 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!83 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!84 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!85 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!86 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!87 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document G1)))))
                                (a!93 (and ((_ is SomeDomain)
                                             (wd_document_domain V1))
                                           (= (url_protocol (wd_location T1))
                                              (url_protocol (wd_location V1)))
                                           (= (@0SomeDomain (wd_document_domain
                                                              T1))
                                              (@0SomeDomain (wd_document_domain
                                                              V1)))))
                                (a!94 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (wd_location T1)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (wd_location T1)))))
                                (a!95 (SomeOrigin (TupleOrigin (url_protocol (wd_location T1))
                                                               (url_host (wd_location T1))
                                                               (url_port (wd_location T1)))))
                                (a!96 (OpaqueOrigin (@0url_path_data (url_path (wd_location T1)))))
                                (a!98 (SomeOrigin (@0url_path_blob (url_path (wd_location T1)))))
                                (a!102 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location V1)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location V1)))))
                                (a!103 (SomeOrigin (TupleOrigin (url_protocol (wd_location V1))
                                                                (url_host (wd_location V1))
                                                                (url_port (wd_location V1)))))
                                (a!104 (OpaqueOrigin (@0url_path_data (url_path (wd_location V1)))))
                                (a!106 (SomeOrigin (@0url_path_blob (url_path (wd_location V1)))))
                                (a!111 (or (not (sc_secure U1))
                                           (= (url_protocol (wd_location V1))
                                              ProtocolHTTPS)))
                                (a!112 (@0domain (@0SomeDomain (url_host (wd_location V1)))))
                                (a!114 ((_ is domain)
                                         (@0SomeDomain (url_host (wd_location V1)))))
                                (a!116 (@0subdomain (@0SomeDomain (url_host (wd_location V1)))))
                                (a!118 (@1subdomain (@0SomeDomain (url_host (wd_location V1)))))
                                (a!122 (= (sc_reg_domain U1)
                                          (@0SomeDomain (url_host (wd_location V1)))))
                                (a!125 (not ((_ is url_path_blob)
                                              (url_path (wd_location V1)))))
                                (a!126 (not ((_ is url_path_data)
                                              (url_path (wd_location V1)))))
                                (a!127 (= (@0url_path_res (url_path (wd_location V1)))
                                          slash))
                                (a!132 (ite (= (frame_window I1) 3)
                                            (@3ArrayWindow (windows Q1))
                                            (ite (= (frame_window I1) 4)
                                                 (@4ArrayWindow (windows Q1))
                                                 (@defaultArrayWindow
                                                   (windows Q1)))))
                                (a!136 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!137 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!138 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!139 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!140 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!141 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                (a!149 (ite (= (frame_window H) 3)
                                            (@3ArrayWindow (windows M))
                                            (ite (= (frame_window H) 4)
                                                 (@4ArrayWindow (windows M))
                                                 (@defaultArrayWindow
                                                   (windows M))))))
                          (let ((a!4 (ite (and a!1 a!2 a!3)
                                          NoneSetCookie
                                          (SomeSetCookie (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            C2)))))
                                (a!8 (ite (and a!5 a!6 a!7)
                                          NoneSetCookie
                                          (SomeSetCookie (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            C2)))))
                                (a!12 (ite (and a!9 a!10 a!11)
                                           NoneSetCookie
                                           (SomeSetCookie (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             C2)))))
                                (a!16 (ite (and a!13 a!14 a!15)
                                           NoneSetCookie
                                           (SomeSetCookie (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             C2)))))
                                (a!20 (ite (and a!17 a!18 a!19)
                                           NoneSetCookie
                                           (SomeSetCookie (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             C2)))))
                                (a!24 (ite (and a!21 a!22 a!23)
                                           NoneSetCookie
                                           (SomeSetCookie (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             C2)))))
                                (a!27 (ite (= F2 1)
                                           (Build_ArrayoptionSetCookie
                                             (@0ArrayoptionSetCookie D2)
                                             (SomeSetCookie G2)
                                             (@2ArrayoptionSetCookie D2)
                                             (@3ArrayoptionSetCookie D2)
                                             (@4ArrayoptionSetCookie D2)
                                             (@defaultArrayoptionSetCookie D2))
                                           (ite (= F2 2)
                                                (Build_ArrayoptionSetCookie
                                                  (@0ArrayoptionSetCookie D2)
                                                  (@1ArrayoptionSetCookie D2)
                                                  (SomeSetCookie G2)
                                                  (@3ArrayoptionSetCookie D2)
                                                  (@4ArrayoptionSetCookie D2)
                                                  (@defaultArrayoptionSetCookie
                                                    D2))
                                                a!26)))
                                (a!30 (= (ite (= F2 0)
                                              (@0ArrayoptionSetCookie D2)
                                              (ite (= F2 1)
                                                   (@1ArrayoptionSetCookie D2)
                                                   a!29))
                                         NoneSetCookie))
                                (a!37 (ite (= B1 2)
                                           a!33
                                           (ite (= B1 3)
                                                a!34
                                                (ite (= B1 4) a!35 a!36))))
                                (a!47 (ite ((_ is url_path_data)
                                             (url_path (wd_location Z1)))
                                           (SomeOrigin a!46)
                                           NoneOrigin))
                                (a!49 (ite ((_ is url_path_blob)
                                             (url_path (wd_location Z1)))
                                           a!48
                                           NoneOrigin))
                                (a!55 (ite ((_ is url_path_data)
                                             (url_path (wd_location B2)))
                                           (SomeOrigin a!54)
                                           NoneOrigin))
                                (a!57 (ite ((_ is url_path_blob)
                                             (url_path (wd_location B2)))
                                           a!56
                                           NoneOrigin))
                                (a!63 (= (@0domain (@0SomeDomain (sc_domain A2)))
                                         a!62))
                                (a!65 (= (@1subdomain (@0SomeDomain (sc_domain A2)))
                                         a!62))
                                (a!67 (= (@0subdomain (@0SomeDomain (sc_domain A2)))
                                         a!66))
                                (a!69 (= (@1subdomain (@0SomeDomain (sc_domain A2)))
                                         a!68))
                                (a!78 (and a!61
                                           (sc_secure A2)
                                           a!75
                                           a!76
                                           ((_ is SomeDomain)
                                             (url_host (wd_location B2)))
                                           a!72
                                           a!77
                                           (= (sc_path A2) slash)
                                           (= (sc_domain A2) NoneDomain)))
                                (a!88 (ite (= F1 2)
                                           a!84
                                           (ite (= F1 3)
                                                a!85
                                                (ite (= F1 4) a!86 a!87))))
                                (a!97 (ite ((_ is url_path_data)
                                             (url_path (wd_location T1)))
                                           (SomeOrigin a!96)
                                           NoneOrigin))
                                (a!99 (ite ((_ is url_path_blob)
                                             (url_path (wd_location T1)))
                                           a!98
                                           NoneOrigin))
                                (a!105 (ite ((_ is url_path_data)
                                              (url_path (wd_location V1)))
                                            (SomeOrigin a!104)
                                            NoneOrigin))
                                (a!107 (ite ((_ is url_path_blob)
                                              (url_path (wd_location V1)))
                                            a!106
                                            NoneOrigin))
                                (a!113 (= (@0domain (@0SomeDomain (sc_domain U1)))
                                          a!112))
                                (a!115 (= (@1subdomain (@0SomeDomain (sc_domain U1)))
                                          a!112))
                                (a!117 (= (@0subdomain (@0SomeDomain (sc_domain U1)))
                                          a!116))
                                (a!119 (= (@1subdomain (@0SomeDomain (sc_domain U1)))
                                          a!118))
                                (a!128 (and a!111
                                            (sc_secure U1)
                                            a!125
                                            a!126
                                            ((_ is SomeDomain)
                                              (url_host (wd_location V1)))
                                            a!122
                                            a!127
                                            (= (sc_path U1) slash)
                                            (= (sc_domain U1) NoneDomain)))
                                (a!133 (ite (= (frame_window I1) 1)
                                            (@1ArrayWindow (windows Q1))
                                            (ite (= (frame_window I1) 2)
                                                 (@2ArrayWindow (windows Q1))
                                                 a!132)))
                                (a!142 (ite (= E 2)
                                            a!138
                                            (ite (= E 3)
                                                 a!139
                                                 (ite (= E 4) a!140 a!141))))
                                (a!150 (ite (= (frame_window H) 1)
                                            (@1ArrayWindow (windows M))
                                            (ite (= (frame_window H) 2)
                                                 (@2ArrayWindow (windows M))
                                                 a!149))))
                          (let ((a!25 (Build_ArrayoptionSetCookie
                                        (ite ((_ is SomeSetCookie)
                                               (@0ArrayoptionSetCookie C2))
                                             a!4
                                             NoneSetCookie)
                                        (ite ((_ is SomeSetCookie)
                                               (@1ArrayoptionSetCookie C2))
                                             a!8
                                             NoneSetCookie)
                                        (ite ((_ is SomeSetCookie)
                                               (@2ArrayoptionSetCookie C2))
                                             a!12
                                             NoneSetCookie)
                                        (ite ((_ is SomeSetCookie)
                                               (@3ArrayoptionSetCookie C2))
                                             a!16
                                             NoneSetCookie)
                                        (ite ((_ is SomeSetCookie)
                                               (@4ArrayoptionSetCookie C2))
                                             a!20
                                             NoneSetCookie)
                                        (ite ((_ is SomeSetCookie)
                                               (@defaultArrayoptionSetCookie C2))
                                             a!24
                                             NoneSetCookie)))
                                (a!28 (= L2
                                         (ite (= F2 0)
                                              (Build_ArrayoptionSetCookie
                                                (SomeSetCookie G2)
                                                (@1ArrayoptionSetCookie D2)
                                                (@2ArrayoptionSetCookie D2)
                                                (@3ArrayoptionSetCookie D2)
                                                (@4ArrayoptionSetCookie D2)
                                                (@defaultArrayoptionSetCookie
                                                  D2))
                                              a!27)))
                                (a!38 (ite (= B1 0)
                                           a!31
                                           (ite (= B1 1) a!32 a!37)))
                                (a!50 (ite ((_ is url_path_data)
                                             (url_path (wd_location Z1)))
                                           NoneOrigin
                                           a!49))
                                (a!58 (ite ((_ is url_path_data)
                                             (url_path (wd_location B2)))
                                           NoneOrigin
                                           a!57))
                                (a!70 (ite ((_ is domain)
                                             (@0SomeDomain (sc_domain A2)))
                                           (and a!63 a!64)
                                           (ite a!64 a!65 (and a!67 a!69))))
                                (a!89 (ite (= F1 0)
                                           a!82
                                           (ite (= F1 1) a!83 a!88)))
                                (a!100 (ite ((_ is url_path_data)
                                              (url_path (wd_location T1)))
                                            NoneOrigin
                                            a!99))
                                (a!108 (ite ((_ is url_path_data)
                                              (url_path (wd_location V1)))
                                            NoneOrigin
                                            a!107))
                                (a!120 (ite ((_ is domain)
                                              (@0SomeDomain (sc_domain U1)))
                                            (and a!113 a!114)
                                            (ite a!114 a!115 (and a!117 a!119))))
                                (a!134 (= (ite (= (frame_window I1) 0)
                                               (@0ArrayWindow (windows Q1))
                                               a!133)
                                          L1))
                                (a!143 (ite (= E 0)
                                            a!136
                                            (ite (= E 1) a!137 a!142)))
                                (a!151 (= (ite (= (frame_window H) 0)
                                               (@0ArrayWindow (windows M))
                                               a!150)
                                          K)))
                          (let ((a!39 (= (@0ContentElementScript
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!38)))
                                         D1))
                                (a!40 (not ((_ is ContentElementHTML)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!38)))))
                                (a!41 (not ((_ is ContentElementImage)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!38)))))
                                (a!51 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location Z1)))
                                           a!47
                                           a!50))
                                (a!59 (ite ((_ is ProtocolData)
                                             (url_protocol (wd_location B2)))
                                           a!55
                                           a!58))
                                (a!71 (or (not ((_ is SomeDomain)
                                                 (sc_domain A2)))
                                          a!70))
                                (a!90 (= (@0ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!89)))
                                         I1))
                                (a!91 (= (@1ContentElementFrame
                                           (@1DOMElementResource
                                             (@0SomeDOMElement a!89)))
                                         H1))
                                (a!92 (not ((_ is ContentElementScript)
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!89)))))
                                (a!101 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location T1)))
                                            a!97
                                            a!100))
                                (a!109 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location V1)))
                                            a!105
                                            a!108))
                                (a!121 (or (not ((_ is SomeDomain)
                                                  (sc_domain U1)))
                                           a!120))
                                (a!130 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!89)))))
                                (a!131 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!89)))))
                                (a!144 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!143)))
                                          H))
                                (a!145 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!143)))
                                          G))
                                (a!146 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!143)))))
                                (a!147 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!143)))))
                                (a!148 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!143))))))
                          (let ((a!60 (and (not (= (ite a!44 a!45 a!51)
                                                   NoneOrigin))
                                           (= (ite a!44 a!45 a!51)
                                              (ite a!52 a!53 a!59))
                                           (not ((_ is SomeDomain)
                                                  (wd_document_domain B2)))))
                                (a!73 (and a!61
                                           a!71
                                           ((_ is SomeDomain)
                                             (url_host (wd_location B2)))
                                           a!72))
                                (a!74 (and a!61
                                           a!71
                                           (sc_secure A2)
                                           ((_ is SomeDomain)
                                             (url_host (wd_location B2)))
                                           a!72))
                                (a!110 (and (not (= (ite a!94 a!95 a!101)
                                                    NoneOrigin))
                                            (= (ite a!94 a!95 a!101)
                                               (ite a!102 a!103 a!109))
                                            (not ((_ is SomeDomain)
                                                   (wd_document_domain V1)))))
                                (a!123 (and a!111
                                            a!121
                                            ((_ is SomeDomain)
                                              (url_host (wd_location V1)))
                                            a!122))
                                (a!124 (and a!111
                                            a!121
                                            (sc_secure U1)
                                            ((_ is SomeDomain)
                                              (url_host (wd_location V1)))
                                            a!122))
                                (a!152 (and a!144
                                            a!145
                                            a!146
                                            a!147
                                            a!148
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!143)))
                                            ((_ is SomeDOMElement) a!143)
                                            (= S F)
                                            (= L Q)
                                            (= Q R)
                                            (= K R)
                                            (= C1 L)
                                            a!151
                                            (= D (DOMPath (consInt E I) J))
                                            (= O (DOMPath I J))
                                            (= O (DOMPath nilInt P))
                                            (= Z D)
                                            (= M N)
                                            (= T M))))
                          (let ((a!79 (ite ((_ is NoPrefix) (sc_name A2))
                                           a!73
                                           (ite ((_ is Secure) (sc_name A2))
                                                a!74
                                                a!78)))
                                (a!129 (ite ((_ is NoPrefix) (sc_name U1))
                                            a!123
                                            (ite ((_ is Secure) (sc_name U1))
                                                 a!124
                                                 a!128)))
                                (a!153 (or (and (= S Y)
                                                (= C1 X)
                                                (= X Y)
                                                (= Z V)
                                                (= V (DOMPath nilInt W))
                                                (= T U))
                                           a!152)))
                          (let ((a!80 (and (or ((_ is SSLax) (sc_same_site A2))
                                               ((_ is SSStrict)
                                                 (sc_same_site A2))
                                               a!42)
                                           (= I2 W1)
                                           (ite ((_ is SomeDomain)
                                                  (wd_document_domain Z1))
                                                a!43
                                                a!60)
                                           a!79
                                           (= S B2)
                                           (= C1 Z1)
                                           (= E2 Y1)
                                           (= Y1 (DOMPath nilInt DOMTopLevel))
                                           (= T X1)
                                           (= G2 A2)))
                                (a!135 (and (or ((_ is SSLax) (sc_same_site U1))
                                                ((_ is SSStrict)
                                                  (sc_same_site U1))
                                                a!81)
                                            (= O1 P1)
                                            (= I2 O1)
                                            a!90
                                            a!91
                                            a!92
                                            (ite ((_ is SomeDomain)
                                                   (wd_document_domain T1))
                                                 a!93
                                                 a!110)
                                            a!129
                                            a!130
                                            a!131
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!89)))
                                            ((_ is SomeDOMElement) a!89)
                                            (= L1 V1)
                                            (= S G1)
                                            (= N1 T1)
                                            (= C1 N1)
                                            a!134
                                            (= E2 E1)
                                            (= E1 (DOMPath (consInt F1 J1) K1))
                                            (= S1 (DOMPath J1 K1))
                                            (= S1 (DOMPath nilInt DOMTopLevel))
                                            (= Q1 R1)
                                            (= T Q1)
                                            (= G2 M1)
                                            (= M1 U1))))
                          (let ((a!154 (and (Reachable T H2 A)
                                            (= A
                                               (Build_State I2 J2 K2 S C2 M2 N2))
                                            (= B
                                               (Build_State (+ 1 I2)
                                                            J2
                                                            K2
                                                            S
                                                            L2
                                                            M2
                                                            N2))
                                            (= D2 a!25)
                                            a!28
                                            a!30
                                            (= Z (DOMPath A1 (DOMIndex B1)))
                                            a!39
                                            ((_ is SomeDOMElement) a!38)
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!38)))
                                            a!40
                                            a!41
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!38)))
                                            (not (sc_http_only G2))
                                            (or a!80 a!135)
                                            a!153
                                            (= C
                                               (consEvent (EvScriptSetCookie
                                                            Z
                                                            E2
                                                            F2
                                                            G2)
                                                          H2)))))
                            (=> a!154 (Reachable T C B))))))))))
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
      (a!6 (Build_URL ProtocolHTTPS
                      (SomeDomain (subdomain 10562 10563))
                      (SomeInt 34887)
                      (url_path_res (anypath 34886))))
      (a!7 (Build_URL ProtocolHTTPS
                      (SomeDomain (subdomain 31945 10563))
                      (SomeInt 34902)
                      (url_path_res slash)))
      (a!8 (Build_URL ProtocolHTTPS
                      (SomeDomain (subdomain 18105 18106))
                      (SomeInt 34898)
                      (url_path_res (anypath 34897))))
      (a!10 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                      (SomeoptionInt (SomeInt 18105))
                                      18106
                                      NoneInt
                                      NonePath)))
      (a!13 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34896)
                                                   (url_path_data 34895 34894)))))
      (a!14 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 34893)
                                                  (url_path_data 34892 34891)))))
      (a!15 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 34890)
                                                  (url_path_data 34889 34888)))))
      (a!17 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 NoneoptionInt
                                                 72863
                                                 (SomeInt 72862)
                                                 NonePath))
                       NoneTrustedTypes))
      (a!19 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                (SomeTrustedTypes (Build_TrustedTypes
                                                    NoneoptionInt
                                                    false)))))
      (a!21 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 148527
                            148528
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!23 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                 NoneoptionInt
                                                 59737
                                                 (SomeInt 59736)
                                                 NonePath))
                       NoneTrustedTypes))
      (a!24 (ContentElementScript
              (Build_Script (Build_URL ProtocolData
                                       NoneDomain
                                       NoneInt
                                       (url_path_data 10 1))
                            11)))
      (a!26 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 149683)
                                              109771
                                              NoneDomain
                                              (domain 149115)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 139219))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 148409)
                                  (url_path_data 150139 150140)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!27 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 149970
                            149971
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!29 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 34885))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 34884)
                                  (url_path_data 34883 34882)))
              NoneCSP
              NoneReferrerPolicy))
      (a!30 (SomeHTMLElement (HTMLScript (Build_URL ProtocolData
                                                    NoneDomain
                                                    NoneInt
                                                    (url_path_data 10 1)))))
      (a!31 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34879)
                                                   (url_path_data 34878 34877)))))
      (a!32 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34876)
                                                   (url_path_data 34875 34874)))))
      (a!33 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 34873)
                                                  (url_path_data 34872 34871)))))
      (a!37 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 150364)
                                                    (url_path_data 150366
                                                                   150367))
                                         148522)))
      (a!38 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 150365)
                                                    (url_path_data 150369
                                                                   150370))
                                         149733)))
      (a!39 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 150378)
                                                    (url_path_data 150359
                                                                   150360))
                                         149675)))
      (a!40 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34873)
                                                   (url_path_data 34872 34871)))))
      (a!44 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34893)
                                                   (url_path_data 34892 34891)))))
      (a!45 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 34890)
                                                   (url_path_data 34889 34888)))))
      (a!53 (pairOriginoptionCSP
              (TupleOrigin ProtocolHTTP (SomeDomain (domain 0)) (SomeInt 0))
              NoneCSP))
      (a!65 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 0))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 2) 10357))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 17901) 1))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 0) 3))
              NoneprodprodEmitterIntInt))
      (a!69 (Build_SetCookie (Host 109038)
                             109031
                             NoneDomain
                             (subdomain 31945 10563)
                             slash
                             true
                             false
                             SSStrict))
      (a!72 (asserted (forall ((A State)
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
                               (E1 Domain)
                               (F1 NestedDOMPath)
                               (G1 listInt)
                               (H1 DOMSelector)
                               (I1 optionDomain)
                               (J1 Window)
                               (K1 Window)
                               (L1 Int)
                               (M1 Global)
                               (N1 NestedDOMPath)
                               (O1 DOMSelector)
                               (P1 Window)
                               (Q1 optionDomain)
                               (R1 Window)
                               (S1 Global)
                               (T1 Window)
                               (U1 Window)
                               (V1 Int)
                               (W1 Int)
                               (X1 Window)
                               (Y1 Frame)
                               (Z1 Int)
                               (A2 HTML)
                               (B2 Window)
                               (C2 Window)
                               (D2 Int)
                               (E2 Global)
                               (F2 NestedDOMPath)
                               (G2 DOMSelector)
                               (H2 Window)
                               (I2 optionDomain)
                               (J2 Window)
                               (K2 Domain)
                               (L2 listEvent)
                               (M2 Int)
                               (N2 FetchEngine)
                               (O2 ServiceWorker)
                               (P2 Window)
                               (Q2 ArrayoptionSetCookie)
                               (R2 ArrayoptionBlob)
                               (S2 ArrayoptionStorageItem))
                        (! (let ((a!1 (Build_State (+ 1 M2) N2 O2 P2 Q2 R2 S2))
                                 (a!2 (@0ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!3 (@1ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!4 (@2ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!5 (@3ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!6 (@4ArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!7 (@defaultArrayoptionDOMElement
                                        (dm_body (dc_dom (wd_document C1)))))
                                 (a!13 (ite ((_ is domain) K2)
                                            (= (@1subdomain E1) (@0domain K2))
                                            (and (= (@0subdomain E1)
                                                    (@0subdomain K2))
                                                 (= (@1subdomain E1)
                                                    (@1subdomain K2)))))
                                 (a!15 (and (= M2 D2)
                                            (= P2 H2)
                                            (= S J2)
                                            (= H2
                                               (Build_Window (wd_nonce J2)
                                                             (wd_parent J2)
                                                             (wd_location J2)
                                                             I2
                                                             (wd_document J2)))
                                            (= C1 C2)
                                            (= Z F2)
                                            (= F2 (DOMPath nilInt G2))
                                            (= T E2)
                                            (= I2 (SomeDomain K2))))
                                 (a!16 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!17 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!18 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!19 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!20 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!21 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document B2)))))
                                 (a!29 (DOMElementResource
                                         (wd_location X1)
                                         (ContentElementFrame
                                           (Build_Frame (frame_src Y1) Z1)
                                           A2)))
                                 (a!35 (ite (= Z1 3)
                                            (@3ArrayWindow (windows S1))
                                            (ite (= Z1 4)
                                                 (@4ArrayWindow (windows S1))
                                                 (@defaultArrayWindow
                                                   (windows S1)))))
                                 (a!38 (ite (= (frame_window Y1) 3)
                                            (@3ArrayWindow (windows S1))
                                            (ite (= (frame_window Y1) 4)
                                                 (@4ArrayWindow (windows S1))
                                                 (@defaultArrayWindow
                                                   (windows S1)))))
                                 (a!42 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!43 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!44 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!45 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!46 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!47 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document F)))))
                                 (a!55 (ite (= (frame_window H) 3)
                                            (@3ArrayWindow (windows M))
                                            (ite (= (frame_window H) 4)
                                                 (@4ArrayWindow (windows M))
                                                 (@defaultArrayWindow
                                                   (windows M))))))
                           (let ((a!8 (ite (= B1 2)
                                           a!4
                                           (ite (= B1 3)
                                                a!5
                                                (ite (= B1 4) a!6 a!7))))
                                 (a!14 (ite ((_ is domain) E1)
                                            (and (= (@0domain E1) (@0domain K2))
                                                 ((_ is domain) K2))
                                            a!13))
                                 (a!22 (ite (= W1 2)
                                            a!18
                                            (ite (= W1 3)
                                                 a!19
                                                 (ite (= W1 4) a!20 a!21))))
                                 (a!30 (ite (= W1 4)
                                            (Build_ArrayoptionDOMElement
                                              a!16
                                              a!17
                                              a!18
                                              a!19
                                              (SomeDOMElement a!29)
                                              a!21)
                                            (dm_body (dc_dom (wd_document B2)))))
                                 (a!36 (ite (= Z1 1)
                                            (@1ArrayWindow (windows S1))
                                            (ite (= Z1 2)
                                                 (@2ArrayWindow (windows S1))
                                                 a!35)))
                                 (a!39 (ite (= (frame_window Y1) 1)
                                            (@1ArrayWindow (windows S1))
                                            (ite (= (frame_window Y1) 2)
                                                 (@2ArrayWindow (windows S1))
                                                 a!38)))
                                 (a!48 (ite (= E 2)
                                            a!44
                                            (ite (= E 3)
                                                 a!45
                                                 (ite (= E 4) a!46 a!47))))
                                 (a!56 (ite (= (frame_window H) 1)
                                            (@1ArrayWindow (windows M))
                                            (ite (= (frame_window H) 2)
                                                 (@2ArrayWindow (windows M))
                                                 a!55))))
                           (let ((a!9 (ite (= B1 0) a!2 (ite (= B1 1) a!3 a!8)))
                                 (a!23 (ite (= W1 0)
                                            a!16
                                            (ite (= W1 1) a!17 a!22)))
                                 (a!31 (ite (= W1 2)
                                            (Build_ArrayoptionDOMElement
                                              a!16
                                              a!17
                                              (SomeDOMElement a!29)
                                              a!19
                                              a!20
                                              a!21)
                                            (ite (= W1 3)
                                                 (Build_ArrayoptionDOMElement
                                                   a!16
                                                   a!17
                                                   a!18
                                                   (SomeDOMElement a!29)
                                                   a!20
                                                   a!21)
                                                 a!30)))
                                 (a!37 (= (ite (= Z1 0)
                                               (@0ArrayWindow (windows S1))
                                               a!36)
                                          T1))
                                 (a!40 (= (ite (= (frame_window Y1) 0)
                                               (@0ArrayWindow (windows S1))
                                               a!39)
                                          X1))
                                 (a!49 (ite (= E 0)
                                            a!42
                                            (ite (= E 1) a!43 a!48)))
                                 (a!57 (= (ite (= (frame_window H) 0)
                                               (@0ArrayWindow (windows M))
                                               a!56)
                                          K)))
                           (let ((a!10 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!9)))
                                          D1))
                                 (a!11 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!9)))))
                                 (a!12 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!9)))))
                                 (a!24 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!23)))
                                          Y1))
                                 (a!25 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!23)))
                                          A2))
                                 (a!26 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!27 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!28 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!23)))))
                                 (a!32 (ite (= W1 0)
                                            (Build_ArrayoptionDOMElement
                                              (SomeDOMElement a!29)
                                              a!17
                                              a!18
                                              a!19
                                              a!20
                                              a!21)
                                            (ite (= W1 1)
                                                 (Build_ArrayoptionDOMElement
                                                   a!16
                                                   (SomeDOMElement a!29)
                                                   a!18
                                                   a!19
                                                   a!20
                                                   a!21)
                                                 a!31)))
                                 (a!50 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!49)))
                                          H))
                                 (a!51 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!49)))
                                          G))
                                 (a!52 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!49)))))
                                 (a!53 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!49)))))
                                 (a!54 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!49))))))
                           (let ((a!33 (Build_DOM (dm_nonce (dc_dom (wd_document B2)))
                                                  (dm_head (dc_dom (wd_document B2)))
                                                  a!32))
                                 (a!58 (and a!50
                                            a!51
                                            a!52
                                            a!53
                                            a!54
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!49)))
                                            ((_ is SomeDOMElement) a!49)
                                            (= Q R)
                                            (= L Q)
                                            (= S F)
                                            (= K R)
                                            (= C1 L)
                                            a!57
                                            (= Z D)
                                            (= D (DOMPath (consInt E I) J))
                                            (= O (DOMPath I J))
                                            (= O (DOMPath nilInt P))
                                            (= T M)
                                            (= M N))))
                           (let ((a!34 (Build_Window (wd_nonce B2)
                                                     (wd_parent B2)
                                                     (wd_location B2)
                                                     (wd_document_domain B2)
                                                     (Build_Document (+ 1 V1)
                                                                     (dc_nonce (wd_document B2))
                                                                     (dc_headers (wd_document B2))
                                                                     (dc_html (wd_document B2))
                                                                     a!33
                                                                     (dc_init (wd_document B2)))))
                                 (a!59 (or (and (= X Y)
                                                (= S Y)
                                                (= C1 X)
                                                (= Z V)
                                                (= V (DOMPath nilInt W))
                                                (= T U))
                                           a!58)))
                           (let ((a!41 (and (= M2 V1)
                                            (= V1 L1)
                                            a!24
                                            a!25
                                            a!26
                                            a!27
                                            a!28
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!23)))
                                            ((_ is SomeDOMElement) a!23)
                                            (= P2 U1)
                                            (= T1 P1)
                                            (= U1 a!34)
                                            (= S B2)
                                            (= P1
                                               (Build_Window (wd_nonce R1)
                                                             (wd_parent R1)
                                                             (wd_location R1)
                                                             Q1
                                                             (wd_document R1)))
                                            (= J1 K1)
                                            (= X1 R1)
                                            (= C1 J1)
                                            a!37
                                            a!40
                                            (= N1 (DOMPath G1 H1))
                                            (= N1 (DOMPath nilInt O1))
                                            (= F1 (DOMPath (consInt W1 G1) H1))
                                            (= Z F1)
                                            (= T S1)
                                            (= S1 M1)
                                            (= I1 Q1)
                                            (= I1 (SomeDomain K2)))))
                           (let ((a!60 (and (Reachable T L2 A)
                                            (= A
                                               (Build_State M2 N2 O2 S Q2 R2 S2))
                                            (= B a!1)
                                            (= (url_host (wd_location C1))
                                               (SomeDomain E1))
                                            (= Z (DOMPath A1 (DOMIndex B1)))
                                            a!10
                                            ((_ is SomeDOMElement) a!9)
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!9)))
                                            a!11
                                            a!12
                                            a!14
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!9)))
                                            (c_domain_relaxation (config T))
                                            (or a!15 a!41)
                                            a!59
                                            (= C
                                               (consEvent (EvScriptDomainRelaxation
                                                            Z
                                                            K2)
                                                          L2)))))
                             (=> a!60 (Reachable T C B))))))))))
                           :weight 0))))
      (a!78 (asserted (forall ((A State)
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
                                 (a!79 (script_nonce (@0ContentElementScript
                                                       (@0SomeContentElement
                                                         (rp_content R1)))))
                                 (a!80 (@0ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!81 (@1ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!82 (@2ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!83 (@3ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!84 (@4ArrayoptionInt (in_body (dc_init (wd_document S1)))))
                                 (a!85 (@defaultArrayoptionInt
                                         (in_body (dc_init (wd_document S1)))))
                                 (a!93 (= (rp_hd_csp (rp_headers R1))
                                          (rp_hd_csp (dc_headers (wd_document O1)))))
                                 (a!95 (= (@1url_path_blob (url_path (rp_url R1)))
                                          0))
                                 (a!96 (= (@1url_path_blob (url_path (rp_url R1)))
                                          1))
                                 (a!97 (= (@1url_path_blob (url_path (rp_url R1)))
                                          2))
                                 (a!98 (= (@1url_path_blob (url_path (rp_url R1)))
                                          3))
                                 (a!99 (= (@1url_path_blob (url_path (rp_url R1)))
                                          4))
                                 (a!107 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content R1)))))
                                 (a!110 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content R1)))))
                                 (a!134 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!135 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!136 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!137 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!138 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!139 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document S1)))))
                                 (a!145 (not ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content R1)))))
                                 (a!146 (SomeDOMElement (DOMElementResource
                                                          (rp_url R1)
                                                          (@0SomeContentElement
                                                            (rp_content R1)))))
                                 (a!147 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!148 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!149 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!150 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!151 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!152 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document S1)))))
                                 (a!159 (ite (= M1 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= M1 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!162 (not (= (rp_hd_content_type
                                                  (rp_headers R1))
                                                NoneContentType)))
                                 (a!164 (not ((_ is SomeURL)
                                               (rp_hd_location (rp_headers V)))))
                                 (a!166 (ite ((_ is EmitterScript)
                                               (ft_emitter R))
                                             (not (= U DOMTopLevel))
                                             (and ((_ is EmitterForm)
                                                    (ft_emitter R))
                                                  (= U DOMTopLevel))))
                                 (a!167 (not ((_ is SomeContentType)
                                               (rp_hd_content_type
                                                 (rp_headers V)))))
                                 (a!168 (image_src (@0ContentElementImage
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!169 (script_src (@0ContentElementScript
                                                      (@0SomeContentElement
                                                        (rp_content V)))))
                                 (a!170 (frame_src (@0ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!174 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeScript
                                             ContentTypeHTML))
                                 (a!179 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!180 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!181 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!182 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!183 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!184 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document G1)))))
                                 (a!190 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url V)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url V)))
                                            (= (rp_hd_csp (rp_headers V))
                                               NoneCSP)))
                                 (a!191 (html_body (@0ContentElementHTML
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!213 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document W)))))
                                 (a!214 ((_ is SomeCSP)
                                          (rp_hd_csp (dc_headers (wd_document W)))))
                                 (a!215 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location W)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location W)))))
                                 (a!216 (SomeOrigin (TupleOrigin (url_protocol (wd_location W))
                                                                 (url_host (wd_location W))
                                                                 (url_port (wd_location W)))))
                                 (a!217 (OpaqueOrigin (@0url_path_data (url_path (wd_location W)))))
                                 (a!219 (SomeOrigin (@0url_path_blob (url_path (wd_location W)))))
                                 (a!252 (script_nonce (@0ContentElementScript
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!253 (@0ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!254 (@1ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!255 (@2ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!256 (@3ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!257 (@4ArrayoptionInt (in_body (dc_init (wd_document W)))))
                                 (a!258 (@defaultArrayoptionInt
                                          (in_body (dc_init (wd_document W)))))
                                 (a!266 (= (rp_hd_csp (rp_headers V))
                                           (rp_hd_csp (dc_headers (wd_document S)))))
                                 (a!268 (= (@1url_path_blob (url_path (rp_url V)))
                                           0))
                                 (a!269 (= (@1url_path_blob (url_path (rp_url V)))
                                           1))
                                 (a!270 (= (@1url_path_blob (url_path (rp_url V)))
                                           2))
                                 (a!271 (= (@1url_path_blob (url_path (rp_url V)))
                                           3))
                                 (a!272 (= (@1url_path_blob (url_path (rp_url V)))
                                           4))
                                 (a!280 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content V)))))
                                 (a!283 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content V)))))
                                 (a!307 (@0ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!308 (@1ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!309 (@2ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!310 (@3ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!311 (@4ArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!312 (@defaultArrayoptionHTMLElement
                                          (html_body (dc_html (wd_document W)))))
                                 (a!318 (not ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))))
                                 (a!319 (SomeDOMElement (DOMElementResource
                                                          (rp_url V)
                                                          (@0SomeContentElement
                                                            (rp_content V)))))
                                 (a!320 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!321 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!322 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!323 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!324 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!325 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document W)))))
                                 (a!334 (DOMElementResource
                                          (rp_url C1)
                                          (ContentElementFrame
                                            (Build_Frame (frame_src D1) E1)
                                            F1)))
                                 (a!340 (ite (= E1 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= E1 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!343 (ite (= Q 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= Q 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!346 (ite (= (frame_window D1) 3)
                                             (@3ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 4)
                                                  (@4ArrayWindow (windows X))
                                                  (@defaultArrayWindow
                                                    (windows X)))))
                                 (a!349 (not (= (rp_hd_content_type
                                                  (rp_headers V))
                                                NoneContentType)))
                                 (a!351 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url I1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url I1)))))
                                 (a!352 (SomeOrigin (TupleOrigin (url_protocol (rp_url I1))
                                                                 (url_host (rp_url I1))
                                                                 (url_port (rp_url I1)))))
                                 (a!353 (OpaqueOrigin (@0url_path_data (url_path (rp_url I1)))))
                                 (a!355 (SomeOrigin (@0url_path_blob (url_path (rp_url I1)))))
                                 (a!359 (ite (= D 3)
                                             (@3ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 4)
                                                  (@4ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  (@defaultArrayprodOriginoptionCSP
                                                    (origin_csp X1)))))
                                 (a!364 (or (and (= U1 DOMTopLevel)
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
                                 (a!61 (= (@0domain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!62 (= (@1subdomain (@0SomeDomain (url_host a!7)))
                                          (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!64 ((_ is SomeProtocol)
                                         (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!65 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!68 ((_ is SomeoptionInt)
                                         (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!69 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!71 (not ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))))
                                 (a!73 (and ((_ is SomeDomain) (url_host a!7))
                                            ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))))
                                 (a!77 (not ((_ is CSPSrcNone)
                                              (@0SomeCSPSrc (csp_script_src a!40)))))
                                 (a!86 (ite (= (@0DOMIndex Q1) 3)
                                            a!83
                                            (ite (= (@0DOMIndex Q1) 4)
                                                 a!84
                                                 a!85)))
                                 (a!100 (ite a!97
                                             (@2ArrayoptionBlob K1)
                                             (ite a!98
                                                  (@3ArrayoptionBlob K1)
                                                  (ite a!99
                                                       (@4ArrayoptionBlob K1)
                                                       (@defaultArrayoptionBlob
                                                         K1)))))
                                 (a!108 (ite (= a!107 3)
                                             (@3ArrayWindow (windows L1))
                                             (ite (= a!107 4)
                                                  (@4ArrayWindow (windows L1))
                                                  (@defaultArrayWindow
                                                    (windows L1)))))
                                 (a!111 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!110)))))
                                 (a!112 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!114 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!110)))))
                                 (a!115 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!117 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!110)))))
                                 (a!118 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!120 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!110)))))
                                 (a!121 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!123 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!110)))))
                                 (a!124 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!126 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!110)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!110)))))
                                 (a!127 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!110)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!110)))))
                                 (a!140 (ite (= (@0DOMIndex Q1) 3)
                                             a!137
                                             (ite (= (@0DOMIndex Q1) 4)
                                                  a!138
                                                  a!139)))
                                 (a!153 (ite (= (@0DOMIndex Q1) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!152
                                               a!147
                                               a!148
                                               a!149
                                               a!146
                                               a!151)
                                             (dm_body (dc_dom (wd_document S1)))))
                                 (a!160 (ite (= M1 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= M1 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!159)))
                                 (a!165 (and a!164
                                             (not ((_ is ResponseNoContent)
                                                    (rp_code V)))))
                                 (a!171 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!169 (rp_url V))
                                             (= a!170 (rp_url V))))
                                 (a!175 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeImage
                                             a!174))
                                 (a!185 (ite (= B1 2)
                                             a!181
                                             (ite (= B1 3)
                                                  a!182
                                                  (ite (= B1 4) a!183 a!184))))
                                 (a!192 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!191)))))
                                 (a!193 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!195 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!191)))))
                                 (a!196 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!198 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!191)))))
                                 (a!199 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!201 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!191)))))
                                 (a!202 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!204 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!191)))))
                                 (a!205 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!207 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!191)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!191)))))
                                 (a!208 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!191)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!191)))))
                                 (a!218 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             (SomeOrigin a!217)
                                             NoneOrigin))
                                 (a!220 (ite ((_ is url_path_blob)
                                               (url_path (wd_location W)))
                                             a!219
                                             NoneOrigin))
                                 (a!223 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!169)))))
                                 (a!224 (ite ((_ is url_path_blob)
                                               (url_path a!169))
                                             (SomeOrigin (@0url_path_blob (url_path a!169)))
                                             NoneOrigin))
                                 (a!228 (= (url_protocol a!169)
                                           (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!229 ((_ is SomePath)
                                          (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!230 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!232 ((_ is SomeInt)
                                          (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!233 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!234 (= (@0domain (@0SomeDomain (url_host a!169)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!235 (= (@1subdomain (@0SomeDomain (url_host a!169)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!237 ((_ is SomeProtocol)
                                          (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!238 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!241 ((_ is SomeoptionInt)
                                          (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!242 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!244 (not ((_ is domain)
                                               (@0SomeDomain (url_host a!169)))))
                                 (a!246 (and ((_ is SomeDomain)
                                               (url_host a!169))
                                             ((_ is domain)
                                               (@0SomeDomain (url_host a!169)))))
                                 (a!250 (not ((_ is CSPSrcNone)
                                               (@0SomeCSPSrc (csp_script_src a!213)))))
                                 (a!259 (ite (= (@0DOMIndex U) 3)
                                             a!256
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!257
                                                  a!258)))
                                 (a!273 (ite a!270
                                             (@2ArrayoptionBlob O)
                                             (ite a!271
                                                  (@3ArrayoptionBlob O)
                                                  (ite a!272
                                                       (@4ArrayoptionBlob O)
                                                       (@defaultArrayoptionBlob
                                                         O)))))
                                 (a!281 (ite (= a!280 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!280 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!284 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!283)))))
                                 (a!285 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@0ArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!287 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!283)))))
                                 (a!288 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!290 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!283)))))
                                 (a!291 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!293 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!283)))))
                                 (a!294 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!296 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!283)))))
                                 (a!297 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!299 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!283)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!283)))))
                                 (a!300 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!283)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!283)))))
                                 (a!313 (ite (= (@0DOMIndex U) 3)
                                             a!310
                                             (ite (= (@0DOMIndex U) 4)
                                                  a!311
                                                  a!312)))
                                 (a!326 (ite (= (@0DOMIndex U) 4)
                                             (Build_ArrayoptionDOMElement
                                               a!325
                                               a!320
                                               a!321
                                               a!322
                                               a!319
                                               a!324)
                                             (dm_body (dc_dom (wd_document W)))))
                                 (a!335 (ite (= B1 4)
                                             (Build_ArrayoptionDOMElement
                                               a!179
                                               a!180
                                               a!181
                                               a!182
                                               (SomeDOMElement a!334)
                                               a!184)
                                             (dm_body (dc_dom (wd_document G1)))))
                                 (a!341 (ite (= E1 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= E1 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!340)))
                                 (a!344 (ite (= Q 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= Q 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!343)))
                                 (a!347 (ite (= (frame_window D1) 1)
                                             (@1ArrayWindow (windows X))
                                             (ite (= (frame_window D1) 2)
                                                  (@2ArrayWindow (windows X))
                                                  a!346)))
                                 (a!354 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             (SomeOrigin a!353)
                                             NoneOrigin))
                                 (a!356 (ite ((_ is url_path_blob)
                                               (url_path (rp_url I1)))
                                             a!355
                                             NoneOrigin))
                                 (a!360 (ite (= D 1)
                                             (@1ArrayprodOriginoptionCSP
                                               (origin_csp X1))
                                             (ite (= D 2)
                                                  (@2ArrayprodOriginoptionCSP
                                                    (origin_csp X1))
                                                  a!359))))
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
                                 (a!63 (ite ((_ is domain)
                                              (@0SomeDomain (url_host a!7)))
                                            a!61
                                            a!62))
                                 (a!70 (= (@0subdomain (@0SomeDomain (url_host a!7)))
                                          (@0SomeInt a!69)))
                                 (a!87 (ite (= (@0DOMIndex Q1) 1)
                                            a!81
                                            (ite (= (@0DOMIndex Q1) 2)
                                                 a!82
                                                 a!86)))
                                 (a!101 (@0SomeBlob (ite a!95
                                                         (@0ArrayoptionBlob K1)
                                                         (ite a!96
                                                              (@1ArrayoptionBlob
                                                                K1)
                                                              a!100))))
                                 (a!103 ((_ is SomeBlob)
                                          (ite a!95
                                               (@0ArrayoptionBlob K1)
                                               (ite a!96
                                                    (@1ArrayoptionBlob K1)
                                                    a!100))))
                                 (a!109 (ite (= a!107 1)
                                             (@1ArrayWindow (windows L1))
                                             (ite (= a!107 2)
                                                  (@2ArrayWindow (windows L1))
                                                  a!108)))
                                 (a!113 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!112))
                                             NoneDOMElement))
                                 (a!116 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!115))
                                             NoneDOMElement))
                                 (a!119 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!118))
                                             NoneDOMElement))
                                 (a!122 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!121))
                                             NoneDOMElement))
                                 (a!125 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!124))
                                             NoneDOMElement))
                                 (a!128 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!110)))
                                             (SomeDOMElement (DOMElementForm a!127))
                                             NoneDOMElement))
                                 (a!141 (ite (= (@0DOMIndex Q1) 1)
                                             a!135
                                             (ite (= (@0DOMIndex Q1) 2)
                                                  a!136
                                                  a!140)))
                                 (a!154 (ite (= (@0DOMIndex Q1) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!152
                                               a!147
                                               a!146
                                               a!149
                                               a!150
                                               a!151)
                                             (ite (= (@0DOMIndex Q1) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!152
                                                    a!147
                                                    a!148
                                                    a!146
                                                    a!150
                                                    a!151)
                                                  a!153)))
                                 (a!161 (= (ite (= M1 0)
                                                (@0ArrayWindow (windows L1))
                                                a!160)
                                           O1))
                                 (a!172 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!168 (rp_url V))
                                             a!171))
                                 (a!176 (ite ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             ContentTypeHTML
                                             a!175))
                                 (a!186 (ite (= B1 0)
                                             a!179
                                             (ite (= B1 1) a!180 a!185)))
                                 (a!194 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!193))
                                             NoneDOMElement))
                                 (a!197 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!196))
                                             NoneDOMElement))
                                 (a!200 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!199))
                                             NoneDOMElement))
                                 (a!203 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!202))
                                             NoneDOMElement))
                                 (a!206 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!205))
                                             NoneDOMElement))
                                 (a!209 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!191)))
                                             (SomeDOMElement (DOMElementForm a!208))
                                             NoneDOMElement))
                                 (a!221 (ite ((_ is url_path_data)
                                               (url_path (wd_location W)))
                                             NoneOrigin
                                             a!220))
                                 (a!225 (ite ((_ is ProtocolData)
                                               (url_protocol a!169))
                                             (ite ((_ is url_path_data)
                                                    (url_path a!169))
                                                  a!223
                                                  NoneOrigin)
                                             (ite ((_ is url_path_data)
                                                    (url_path a!169))
                                                  NoneOrigin
                                                  a!224)))
                                 (a!231 (and (not ((_ is url_path_blob)
                                                    (url_path a!169)))
                                             (not ((_ is url_path_data)
                                                    (url_path a!169)))
                                             (= (@0url_path_res (url_path a!169))
                                                a!230)))
                                 (a!236 (ite ((_ is domain)
                                               (@0SomeDomain (url_host a!169)))
                                             a!234
                                             a!235))
                                 (a!243 (= (@0subdomain (@0SomeDomain (url_host a!169)))
                                           (@0SomeInt a!242)))
                                 (a!260 (ite (= (@0DOMIndex U) 1)
                                             a!254
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!255
                                                  a!259)))
                                 (a!274 (@0SomeBlob (ite a!268
                                                         (@0ArrayoptionBlob O)
                                                         (ite a!269
                                                              (@1ArrayoptionBlob
                                                                O)
                                                              a!273))))
                                 (a!276 ((_ is SomeBlob)
                                          (ite a!268
                                               (@0ArrayoptionBlob O)
                                               (ite a!269
                                                    (@1ArrayoptionBlob O)
                                                    a!273))))
                                 (a!282 (ite (= a!280 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!280 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!281)))
                                 (a!286 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!285))
                                             NoneDOMElement))
                                 (a!289 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!288))
                                             NoneDOMElement))
                                 (a!292 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!291))
                                             NoneDOMElement))
                                 (a!295 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!294))
                                             NoneDOMElement))
                                 (a!298 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!297))
                                             NoneDOMElement))
                                 (a!301 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!283)))
                                             (SomeDOMElement (DOMElementForm a!300))
                                             NoneDOMElement))
                                 (a!314 (ite (= (@0DOMIndex U) 1)
                                             a!308
                                             (ite (= (@0DOMIndex U) 2)
                                                  a!309
                                                  a!313)))
                                 (a!327 (ite (= (@0DOMIndex U) 2)
                                             (Build_ArrayoptionDOMElement
                                               a!325
                                               a!320
                                               a!319
                                               a!322
                                               a!323
                                               a!324)
                                             (ite (= (@0DOMIndex U) 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!325
                                                    a!320
                                                    a!321
                                                    a!319
                                                    a!323
                                                    a!324)
                                                  a!326)))
                                 (a!336 (ite (= B1 2)
                                             (Build_ArrayoptionDOMElement
                                               a!179
                                               a!180
                                               (SomeDOMElement a!334)
                                               a!182
                                               a!183
                                               a!184)
                                             (ite (= B1 3)
                                                  (Build_ArrayoptionDOMElement
                                                    a!179
                                                    a!180
                                                    a!181
                                                    (SomeDOMElement a!334)
                                                    a!183
                                                    a!184)
                                                  a!335)))
                                 (a!342 (= (ite (= E1 0)
                                                (@0ArrayWindow (windows X))
                                                a!341)
                                           Y))
                                 (a!345 (= (ite (= Q 0)
                                                (@0ArrayWindow (windows P))
                                                a!344)
                                           S))
                                 (a!348 (= (ite (= (frame_window D1) 0)
                                                (@0ArrayWindow (windows X))
                                                a!347)
                                           I))
                                 (a!357 (ite ((_ is url_path_data)
                                               (url_path (rp_url I1)))
                                             NoneOrigin
                                             a!356))
                                 (a!361 (= (ite (= D 0)
                                                (@0ArrayprodOriginoptionCSP
                                                  (origin_csp X1))
                                                a!360)
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
                                 (a!72 (ite ((_ is SomeInt) a!69)
                                            (and a!70
                                                 ((_ is SomeDomain)
                                                   (url_host a!7))
                                                 a!71)
                                            (and ((_ is SomeDomain)
                                                   (url_host a!7))
                                                 a!71)))
                                 (a!88 ((_ is SomeInt)
                                         (ite (= (@0DOMIndex Q1) 0) a!80 a!87)))
                                 (a!89 (@0SomeInt (ite (= (@0DOMIndex Q1) 0)
                                                       a!80
                                                       a!87)))
                                 (a!129 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!111 NoneDOMElement a!113)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!114 NoneDOMElement a!116)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!117 NoneDOMElement a!119)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!120 NoneDOMElement a!122)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!123 NoneDOMElement a!125)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!110))
                                               (ite a!126 NoneDOMElement a!128)
                                               NoneDOMElement)))
                                 (a!142 (@0SomeHTMLElement
                                          (ite (= (@0DOMIndex Q1) 0)
                                               a!134
                                               a!141)))
                                 (a!155 (ite (= (@0DOMIndex Q1) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!146
                                               a!147
                                               a!148
                                               a!149
                                               a!150
                                               a!151)
                                             (ite (= (@0DOMIndex Q1) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!152
                                                    a!146
                                                    a!148
                                                    a!149
                                                    a!150
                                                    a!151)
                                                  a!154)))
                                 (a!158 ((_ is SomeHTMLElement)
                                          (ite (= (@0DOMIndex Q1) 0)
                                               a!134
                                               a!141)))
                                 (a!173 (or ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            a!172))
                                 (a!177 (= a!176
                                           (@0SomeContentType
                                             (rp_hd_content_type (rp_headers V)))))
                                 (a!187 (= (@0ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!186)))
                                           D1))
                                 (a!188 (= (@1ContentElementFrame
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!186)))
                                           F1))
                                 (a!189 (not ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!186)))))
                                 (a!210 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!192 NoneDOMElement a!194)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!195 NoneDOMElement a!197)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!198 NoneDOMElement a!200)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!201 NoneDOMElement a!203)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!204 NoneDOMElement a!206)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!191))
                                               (ite a!207 NoneDOMElement a!209)
                                               NoneDOMElement)))
                                 (a!222 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location W)))
                                             a!218
                                             a!221))
                                 (a!226 (ite (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!169))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!169)))
                                             (SomeOrigin (TupleOrigin (url_protocol a!169)
                                                                      (url_host a!169)
                                                                      (url_port a!169)))
                                             a!225))
                                 (a!245 (ite ((_ is SomeInt) a!242)
                                             (and a!243
                                                  ((_ is SomeDomain)
                                                    (url_host a!169))
                                                  a!244)
                                             (and ((_ is SomeDomain)
                                                    (url_host a!169))
                                                  a!244)))
                                 (a!261 ((_ is SomeInt)
                                          (ite (= (@0DOMIndex U) 0) a!253 a!260)))
                                 (a!262 (@0SomeInt (ite (= (@0DOMIndex U) 0)
                                                        a!253
                                                        a!260)))
                                 (a!302 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!284 NoneDOMElement a!286)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!287 NoneDOMElement a!289)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!290 NoneDOMElement a!292)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!293 NoneDOMElement a!295)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!296 NoneDOMElement a!298)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!283))
                                               (ite a!299 NoneDOMElement a!301)
                                               NoneDOMElement)))
                                 (a!315 (@0SomeHTMLElement
                                          (ite (= (@0DOMIndex U) 0) a!307 a!314)))
                                 (a!328 (ite (= (@0DOMIndex U) 0)
                                             (Build_ArrayoptionDOMElement
                                               a!319
                                               a!320
                                               a!321
                                               a!322
                                               a!323
                                               a!324)
                                             (ite (= (@0DOMIndex U) 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!325
                                                    a!319
                                                    a!321
                                                    a!322
                                                    a!323
                                                    a!324)
                                                  a!327)))
                                 (a!331 ((_ is SomeHTMLElement)
                                          (ite (= (@0DOMIndex U) 0) a!307 a!314)))
                                 (a!332 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!186)))))
                                 (a!333 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!186)))))
                                 (a!337 (ite (= B1 0)
                                             (Build_ArrayoptionDOMElement
                                               (SomeDOMElement a!334)
                                               a!180
                                               a!181
                                               a!182
                                               a!183
                                               a!184)
                                             (ite (= B1 1)
                                                  (Build_ArrayoptionDOMElement
                                                    a!179
                                                    (SomeDOMElement a!334)
                                                    a!181
                                                    a!182
                                                    a!183
                                                    a!184)
                                                  a!336)))
                                 (a!358 (ite ((_ is ProtocolData)
                                               (url_protocol (rp_url I1)))
                                             a!354
                                             a!357)))
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
                                 (a!66 (not ((_ is TupleOrigin)
                                              (@0SomeOrigin (ite a!42 a!43 a!49)))))
                                 (a!67 (= (url_protocol a!7)
                                          (@0TupleOrigin (@0SomeOrigin (ite a!42
                                                                            a!43
                                                                            a!49)))))
                                 (a!90 (ite (= a!89 3)
                                            (@3ArrayWindow (windows L1))
                                            (ite (= a!89 4)
                                                 (@4ArrayWindow (windows L1))
                                                 (@defaultArrayWindow
                                                   (windows L1)))))
                                 (a!130 (Build_Document (+ 1 P1)
                                                        (ft_correlator N1)
                                                        (rp_headers R1)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content R1)))
                                                        (Build_DOM (ft_correlator N1)
                                                                   0
                                                                   a!129)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!143 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (= a!142 (HTMLScript a!7))
                                             (= a!142 (HTMLFrame a!8))))
                                 (a!156 (Build_DOM (dm_nonce (dc_dom (wd_document S1)))
                                                   (dm_head (dc_dom (wd_document S1)))
                                                   a!155))
                                 (a!178 (or (not ((_ is SomeContentElement)
                                                   (rp_content V)))
                                            a!167
                                            (and a!173 a!177)))
                                 (a!211 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@0ContentElementHTML
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!210)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!227 (= (SomeOrigin (@0SomeOrigin (ite a!215
                                                                          a!216
                                                                          a!222)))
                                           a!226))
                                 (a!239 (not ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!215
                                                                  a!216
                                                                  a!222)))))
                                 (a!240 (= (url_protocol a!169)
                                           (@0TupleOrigin (@0SomeOrigin (ite a!215
                                                                             a!216
                                                                             a!222)))))
                                 (a!263 (ite (= a!262 3)
                                             (@3ArrayWindow (windows P))
                                             (ite (= a!262 4)
                                                  (@4ArrayWindow (windows P))
                                                  (@defaultArrayWindow
                                                    (windows P)))))
                                 (a!303 (Build_Document (+ 1 T)
                                                        (ft_correlator R)
                                                        (rp_headers V)
                                                        (@1ContentElementFrame
                                                          (@0SomeContentElement
                                                            (rp_content V)))
                                                        (Build_DOM (ft_correlator R)
                                                                   0
                                                                   a!302)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                 (a!316 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!315 (HTMLScript a!169))
                                             (= a!315 (HTMLFrame a!170))))
                                 (a!329 (Build_DOM (dm_nonce (dc_dom (wd_document W)))
                                                   (dm_head (dc_dom (wd_document W)))
                                                   a!328))
                                 (a!338 (Build_DOM (dm_nonce (dc_dom (wd_document G1)))
                                                   (dm_head (dc_dom (wd_document G1)))
                                                   a!337))
                                 (a!362 (and (c_origin_wide_csp (config X1))
                                             (= (ite a!351 a!352 a!358)
                                                (SomeOrigin F))
                                             a!361
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
                                 (a!74 (and (or (not a!56) a!58)
                                            (or (not a!59)
                                                (= (url_port a!7)
                                                   (SomeInt a!60)))
                                            a!63
                                            (ite a!64
                                                 (= (url_protocol a!7) a!65)
                                                 (or a!66 a!67))
                                            (ite a!68 a!72 a!73)
                                            ((_ is SomeDomain) (url_host a!7))))
                                 (a!91 (ite (= a!89 1)
                                            (@1ArrayWindow (windows L1))
                                            (ite (= a!89 2)
                                                 (@2ArrayWindow (windows L1))
                                                 a!90)))
                                 (a!131 (= (ite (= a!107 0)
                                                (@0ArrayWindow (windows L1))
                                                a!109)
                                           (Build_Window (ft_correlator N1)
                                                         (SomeInt M1)
                                                         (rp_url R1)
                                                         NoneDomain
                                                         a!130)))
                                 (a!144 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (= a!142 (HTMLImage a!6))
                                             a!143))
                                 (a!157 (Build_Window (wd_nonce S1)
                                                      (wd_parent S1)
                                                      (wd_location S1)
                                                      (wd_document_domain S1)
                                                      (Build_Document (+ 1 P1)
                                                                      (dc_nonce (wd_document S1))
                                                                      (dc_headers (wd_document S1))
                                                                      (dc_html (wd_document S1))
                                                                      a!156
                                                                      (dc_init (wd_document S1)))))
                                 (a!212 (and a!190
                                             ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= S
                                                (Build_Window (ft_correlator R)
                                                              NoneInt
                                                              (rp_url V)
                                                              NoneDomain
                                                              a!211))))
                                 (a!247 (and (or (not a!229) a!231)
                                             (or (not a!232)
                                                 (= (url_port a!169)
                                                    (SomeInt a!233)))
                                             a!236
                                             (ite a!237
                                                  (= (url_protocol a!169) a!238)
                                                  (or a!239 a!240))
                                             (ite a!241 a!245 a!246)
                                             ((_ is SomeDomain)
                                               (url_host a!169))))
                                 (a!264 (ite (= a!262 1)
                                             (@1ArrayWindow (windows P))
                                             (ite (= a!262 2)
                                                  (@2ArrayWindow (windows P))
                                                  a!263)))
                                 (a!304 (= (ite (= a!280 0)
                                                (@0ArrayWindow (windows P))
                                                a!282)
                                           (Build_Window (ft_correlator R)
                                                         (SomeInt Q)
                                                         (rp_url V)
                                                         NoneDomain
                                                         a!303)))
                                 (a!317 (ite ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (= a!315 (HTMLImage a!168))
                                             a!316))
                                 (a!330 (Build_Window (wd_nonce W)
                                                      (wd_parent W)
                                                      (wd_location W)
                                                      (wd_document_domain W)
                                                      (Build_Document (+ 1 T)
                                                                      (dc_nonce (wd_document W))
                                                                      (dc_headers (wd_document W))
                                                                      (dc_html (wd_document W))
                                                                      a!329
                                                                      (dc_init (wd_document W)))))
                                 (a!339 (Build_Window (wd_nonce G1)
                                                      (wd_parent G1)
                                                      (wd_location G1)
                                                      (wd_document_domain G1)
                                                      (Build_Document (+ 1 A1)
                                                                      (dc_nonce (wd_document G1))
                                                                      (dc_headers (wd_document G1))
                                                                      (dc_html (wd_document G1))
                                                                      a!338
                                                                      (dc_init (wd_document G1)))))
                                 (a!363 (or (not (c_origin_wide_csp (config X1)))
                                            a!362)))
                           (let ((a!75 (ite ((_ is CSPSrcScheme)
                                              (@0SomeCSPSrc (csp_script_src a!40)))
                                            a!55
                                            a!74))
                                 (a!92 (wd_document (ite (= a!89 0)
                                                         (@0ArrayWindow (windows L1))
                                                         a!91)))
                                 (a!248 (ite ((_ is CSPSrcScheme)
                                               (@0SomeCSPSrc (csp_script_src a!213)))
                                             a!228
                                             a!247))
                                 (a!265 (wd_document (ite (= a!262 0)
                                                          (@0ArrayWindow (windows P))
                                                          a!264))))
                           (let ((a!76 (ite ((_ is CSPSrcSelf)
                                              (@0SomeCSPSrc (csp_script_src a!40)))
                                            a!54
                                            a!75))
                                 (a!94 (ite (c_csp_inherit_local_from_initiator
                                              (config L1))
                                            (= (rp_hd_csp (rp_headers R1))
                                               (rp_hd_csp (dc_headers a!92)))
                                            a!93))
                                 (a!249 (ite ((_ is CSPSrcSelf)
                                               (@0SomeCSPSrc (csp_script_src a!213)))
                                             a!227
                                             a!248))
                                 (a!267 (ite (c_csp_inherit_local_from_initiator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (rp_hd_csp (dc_headers a!265)))
                                             a!266)))
                           (let ((a!78 (or (not ((_ is SomeCSPSrc)
                                                  (csp_script_src a!40)))
                                           (not a!41)
                                           (and a!76
                                                ((_ is SomeOrigin)
                                                  (ite a!42 a!43 a!49))
                                                a!77)))
                                 (a!102 (ite (c_csp_inherit_blob_from_creator
                                               (config L1))
                                             (= (rp_hd_csp (rp_headers R1))
                                                (blob_csp a!101))
                                             (ite a!88 a!94 a!93)))
                                 (a!251 (or (not ((_ is SomeCSPSrc)
                                                   (csp_script_src a!213)))
                                            (not a!214)
                                            (and a!249
                                                 ((_ is SomeOrigin)
                                                   (ite a!215 a!216 a!222))
                                                 a!250)))
                                 (a!275 (ite (c_csp_inherit_blob_from_creator
                                               (config P))
                                             (= (rp_hd_csp (rp_headers V))
                                                (blob_csp a!274))
                                             (ite a!261 a!267 a!266))))
                           (let ((a!104 (ite ((_ is url_path_blob)
                                               (url_path (rp_url R1)))
                                             (and a!102 a!103)
                                             (ite a!88 a!94 a!93)))
                                 (a!277 (ite ((_ is url_path_blob)
                                               (url_path (rp_url V)))
                                             (and a!275 a!276)
                                             (ite a!261 a!267 a!266))))
                           (let ((a!105 (ite ((_ is url_path_data)
                                               (url_path (rp_url R1)))
                                             (ite a!88 a!94 a!93)
                                             a!104))
                                 (a!278 (ite ((_ is url_path_data)
                                               (url_path (rp_url V)))
                                             (ite a!261 a!267 a!266)
                                             a!277)))
                           (let ((a!106 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url R1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url R1)))
                                            a!105))
                                 (a!279 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url V)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url V)))
                                            a!278)))
                           (let ((a!132 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content R1)))
                                             (and a!78 (= a!79 P1))
                                             (and a!106 a!131)))
                                 (a!305 (ite ((_ is ContentElementScript)
                                               (@0SomeContentElement
                                                 (rp_content V)))
                                             (and a!251 (= a!252 T))
                                             (and a!279 a!304))))
                           (let ((a!133 (or ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content R1)))
                                            a!132))
                                 (a!306 (or ((_ is ContentElementImage)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            ((_ is ContentElementHTML)
                                              (@0SomeContentElement
                                                (rp_content V)))
                                            a!305)))
                           (let ((a!163 (and (or ((_ is ResponseOk)
                                                   (rp_code R1))
                                                 a!3)
                                             (or ((_ is EmitterClient)
                                                   (ft_emitter N1))
                                                 a!4)
                                             a!16
                                             (= A2 P1)
                                             (ite ((_ is DOMTopLevel) Q1)
                                                  a!39
                                                  (and a!133
                                                       a!144
                                                       a!145
                                                       (= O1 a!157)
                                                       a!158))
                                             (= D2 O1)
                                             (= H1 S1)
                                             a!161
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
                                             a!162
                                             (= W1 K1)))
                                 (a!350 (and (or ((_ is ResponseOk) (rp_code V))
                                                 a!165)
                                             (or ((_ is EmitterClient)
                                                   (ft_emitter R))
                                                 a!166)
                                             a!178
                                             (= A2 A1)
                                             (= A1 T)
                                             a!187
                                             a!188
                                             a!189
                                             (ite ((_ is DOMTopLevel) U)
                                                  a!212
                                                  (and a!306
                                                       a!317
                                                       a!318
                                                       (= S a!330)
                                                       a!331))
                                             a!332
                                             a!333
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!186)))
                                             ((_ is SomeDOMElement) a!186)
                                             (= D2 Z)
                                             (= H1 G1)
                                             (= Z a!339)
                                             (= Y S)
                                             (= I W)
                                             a!342
                                             a!345
                                             a!348
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
                                             a!349
                                             (= W1 L)
                                             (= L O))))
                           (let ((a!365 (and (Reachable X1 Z1 A)
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
                                             (or a!163 a!350)
                                             a!363
                                             a!364
                                             (= C
                                                (consEvent (EvDOMUpdate Y1) Z1)))))
                             (=> a!365 (Reachable X1 C B))))))))))))))))))
                           :weight 0))))
      (a!81 (asserted (forall ((A Script)
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
                                            (= A3 T2)
                                            (= T2 U2)))
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
                                            (= Y (DOMPath Z (DOMIndex A1)))
                                            (= B Y)
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
                                             (= G3 (DOMPath H3 (DOMIndex I3)))
                                             (= J2 G3)
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
      (a!82 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 0))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 2) 10357))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 17901) 1))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!84 (asserted (forall ((A Script)
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
      (a!89 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 0))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 2) 10357))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!96 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 0))
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
      (a!108 (asserted (forall ((A Global))
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
                               (E Bool)
                               (F Bool)
                               (G Bool)
                               (H Bool)
                               (I Bool)
                               (J Bool)
                               (K Bool)
                               (L Bool)
                               (M Bool)
                               (N Bool)
                               (O Bool)
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
                               (Z Bool))
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
                                 (a!3 (Build_URL ProtocolHTTPS
                                                 (SomeDomain (subdomain 10562
                                                                        10563))
                                                 (SomeInt 34887)
                                                 (url_path_res (anypath 34886))))
                                 (a!4 (Build_URL ProtocolHTTPS
                                                 (SomeDomain (subdomain 31945
                                                                        10563))
                                                 (SomeInt 34902)
                                                 (url_path_res slash)))
                                 (a!5 (Build_URL ProtocolHTTPS
                                                 (SomeDomain (subdomain 18105
                                                                        18106))
                                                 (SomeInt 34898)
                                                 (url_path_res (anypath 34897))))
                                 (a!7 (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                (SomeoptionInt (SomeInt 18105))
                                                                18106
                                                                NoneInt
                                                                NonePath)))
                                 (a!10 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34896)
                                                                              (url_path_data 34895
                                                                                             34894)))))
                                 (a!11 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 34893)
                                                                             (url_path_data 34892
                                                                                            34891)))))
                                 (a!12 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 34890)
                                                                             (url_path_data 34889
                                                                                            34888)))))
                                 (a!14 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            72863
                                                                            (SomeInt 72862)
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                 (a!16 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                                           (SomeTrustedTypes (Build_TrustedTypes
                                                                               NoneoptionInt
                                                                               false)))))
                                 (a!18 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 148527
                                                       148528
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!20 (Build_CSP (SomeCSPSrc (CSPSrcSource NoneProtocol
                                                                            NoneoptionInt
                                                                            59737
                                                                            (SomeInt 59736)
                                                                            NonePath))
                                                  NoneTrustedTypes))
                                 (a!21 (ContentElementScript
                                         (Build_Script (Build_URL ProtocolData
                                                                  NoneDomain
                                                                  NoneInt
                                                                  (url_path_data 10
                                                                                 1))
                                                       11)))
                                 (a!23 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 149683)
                                                                         109771
                                                                         NoneDomain
                                                                         (domain 149115)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         (SomeOrigin (OpaqueOrigin 139219))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 148409)
                                                             (url_path_data 150139
                                                                            150140)))
                                         (SomeCSP (Build_CSP NoneCSPSrc
                                                             NoneTrustedTypes))
                                         NoneReferrerPolicy))
                                 (a!24 (SomeContentElement
                                         (ContentElementHTML
                                           (Build_HTML 149970
                                                       149971
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!26 (Build_ResponseHeaders
                                         (SomeContentType ContentTypeHTML)
                                         NoneSetCookie
                                         (SomeOrigin (OpaqueOrigin 34885))
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 34884)
                                                             (url_path_data 34883
                                                                            34882)))
                                         NoneCSP
                                         NoneReferrerPolicy))
                                 (a!27 (SomeHTMLElement (HTMLScript (Build_URL ProtocolData
                                                                               NoneDomain
                                                                               NoneInt
                                                                               (url_path_data 10
                                                                                              1)))))
                                 (a!28 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34879)
                                                                              (url_path_data 34878
                                                                                             34877)))))
                                 (a!29 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34876)
                                                                              (url_path_data 34875
                                                                                             34874)))))
                                 (a!30 (SomeHTMLElement (HTMLForm MethodGet
                                                                  (Build_URL ProtocolHTTP
                                                                             NoneDomain
                                                                             (SomeInt 34873)
                                                                             (url_path_data 34872
                                                                                            34871)))))
                                 (a!34 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 150364)
                                                                               (url_path_data 150366
                                                                                              150367))
                                                                    148522)))
                                 (a!35 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 150365)
                                                                               (url_path_data 150369
                                                                                              150370))
                                                                    149733)))
                                 (a!36 (EmitterScript (DOMPath nilInt
                                                               DOMTopLevel)
                                                      (Build_Script (Build_URL ProtocolHTTP
                                                                               NoneDomain
                                                                               (SomeInt 150378)
                                                                               (url_path_data 150359
                                                                                              150360))
                                                                    149675)))
                                 (a!37 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34873)
                                                                              (url_path_data 34872
                                                                                             34871)))))
                                 (a!41 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34893)
                                                                              (url_path_data 34892
                                                                                             34891)))))
                                 (a!42 (DOMElementForm (Build_Form MethodGet
                                                                   (Build_URL ProtocolHTTP
                                                                              NoneDomain
                                                                              (SomeInt 34890)
                                                                              (url_path_data 34889
                                                                                             34888)))))
                                 (a!50 (pairOriginoptionCSP
                                         (TupleOrigin ProtocolHTTP
                                                      (SomeDomain (domain 0))
                                                      (SomeInt 0))
                                         NoneCSP))
                                 (a!52 (Build_SetCookie (Host 109038)
                                                        109031
                                                        NoneDomain
                                                        (subdomain 31945 10563)
                                                        slash
                                                        true
                                                        false
                                                        SSStrict))
                                 (a!64 (Build_ArrayoptionprodprodEmitterIntInt
                                         NoneprodprodEmitterIntInt
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 4)
                                             0))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 2)
                                             10357))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient
                                                             17901)
                                             1))
                                         (SomeprodprodEmitterIntInt
                                           (pairprodEmitterIntInt
                                             (pairEmitterInt EmitterClient 0)
                                             3))
                                         NoneprodprodEmitterIntInt))
                                 (a!68 (Build_Document 7143
                                                       7144
                                                       (Build_ResponseHeaders
                                                         NoneContentType
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         NoneCSP
                                                         NoneReferrerPolicy)
                                                       (Build_HTML 7139
                                                                   7140
                                                                   (Build_ArrayoptionHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement
                                                                     NoneHTMLElement))
                                                       (Build_DOM 7141
                                                                  7142
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement))
                                                       (Build_Initiators (SomeInt 96012)
                                                                         (Build_ArrayoptionInt
                                                                           (SomeInt 96011)
                                                                           (SomeInt 96010)
                                                                           (SomeInt 96009)
                                                                           (SomeInt 96008)
                                                                           (SomeInt 96007)
                                                                           (SomeInt 96006)))))
                                 (a!92 (= (DOMPath (consInt 0 nilInt)
                                                   (DOMIndex 0))
                                          (DOMPath (consInt 0 nilInt)
                                                   (DOMIndex 0)))))
                           (let ((a!2 (Build_Request MethodGet
                                                     (Build_URL ProtocolData
                                                                NoneDomain
                                                                NoneInt
                                                                (url_path_data 10
                                                                               1))
                                                     a!1
                                                     (SomeInt 141637)))
                                 (a!8 (SomeCSP (Build_CSP a!7
                                                          (SomeTrustedTypes (Build_TrustedTypes
                                                                              NoneoptionInt
                                                                              false)))))
                                 (a!13 (Build_HTML 34900
                                                   34899
                                                   (Build_ArrayoptionHTMLElement
                                                     (SomeHTMLElement (HTMLFrame a!3))
                                                     (SomeHTMLElement (HTMLScript a!5))
                                                     a!10
                                                     a!11
                                                     NoneHTMLElement
                                                     a!12)))
                                 (a!15 (Build_Response a!5
                                                       ResponseOk
                                                       (Build_ResponseHeaders
                                                         (SomeContentType ContentTypeScript)
                                                         NoneSetCookie
                                                         (SomeOrigin (OpaqueOrigin 72864))
                                                         NoneURL
                                                         (SomeCSP a!14)
                                                         NoneReferrerPolicy)
                                                       (SomeContentElement
                                                         (ContentElementScript
                                                           (Build_Script a!5 8)))))
                                 (a!17 (Build_ResponseHeaders
                                         NoneContentType
                                         (SomeSetCookie (Build_SetCookie (NoPrefix 149824)
                                                                         109770
                                                                         NoneDomain
                                                                         (domain 148848)
                                                                         slash
                                                                         false
                                                                         false
                                                                         SSStrict))
                                         NoneOrigin
                                         (SomeURL (Build_URL ProtocolHTTP
                                                             NoneDomain
                                                             (SomeInt 148975)
                                                             (url_path_data 150105
                                                                            150106)))
                                         a!16
                                         NoneReferrerPolicy))
                                 (a!22 (Build_Response (Build_URL ProtocolData
                                                                  NoneDomain
                                                                  NoneInt
                                                                  (url_path_data 10
                                                                                 1))
                                                       ResponseOk
                                                       (Build_ResponseHeaders
                                                         (SomeContentType ContentTypeScript)
                                                         NoneSetCookie
                                                         NoneOrigin
                                                         NoneURL
                                                         (SomeCSP a!20)
                                                         NoneReferrerPolicy)
                                                       (SomeContentElement a!21)))
                                 (a!25 (Build_Response (Build_URL ProtocolHTTP
                                                                  (SomeDomain (domain 148287))
                                                                  (SomeInt 135246)
                                                                  (url_path_data 123291
                                                                                 123292))
                                                       ResponseOk
                                                       a!23
                                                       a!24))
                                 (a!31 (Build_HTML 34881
                                                   34880
                                                   (Build_ArrayoptionHTMLElement
                                                     a!27
                                                     NoneHTMLElement
                                                     NoneHTMLElement
                                                     a!28
                                                     a!29
                                                     a!30)))
                                 (a!40 (SomeDOMElement (DOMElementResource
                                                         a!5
                                                         (ContentElementScript
                                                           (Build_Script a!5 8)))))
                                 (a!44 (SomeDOMElement (DOMElementResource
                                                         (Build_URL ProtocolData
                                                                    NoneDomain
                                                                    NoneInt
                                                                    (url_path_data 10
                                                                                   1))
                                                         a!21)))
                                 (a!49 (Build_ArrayContentElement
                                         (ContentElementHTML
                                           (Build_HTML 112476
                                                       112477
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         a!21
                                         (ContentElementHTML
                                           (Build_HTML 111288
                                                       111289
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 111218
                                                       111219
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 129042
                                                       129043
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))
                                         (ContentElementHTML
                                           (Build_HTML 125128
                                                       125129
                                                       (Build_ArrayoptionHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement
                                                         NoneHTMLElement)))))
                                 (a!54 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!4
                                                                            a!1
                                                                            (SomeInt 110606))
                                                             1)
                                                  nilEvent))
                                 (a!69 (Build_Window 109032
                                                     (SomeInt 96629)
                                                     (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 66290)
                                                                (url_path_data 66289
                                                                               66288))
                                                     (SomeDomain (domain 102665))
                                                     a!68))
                                 (a!70 (Build_Window 109033
                                                     (SomeInt 96629)
                                                     (Build_URL ProtocolHTTP
                                                                NoneDomain
                                                                (SomeInt 66290)
                                                                (url_path_data 66289
                                                                               66288))
                                                     (SomeDomain (domain 102665))
                                                     a!68)))
                           (let ((a!6 (Build_ArrayRequest
                                        a!2
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 123989)
                                                                  (url_path_res slash))
                                                       a!1
                                                       (SomeInt 120694))
                                        (Build_Request MethodGet
                                                       a!3
                                                       a!1
                                                       (SomeInt 132535))
                                        (Build_Request MethodGet
                                                       (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 110500)
                                                                  (url_path_data 4572
                                                                                 109769))
                                                       a!1
                                                       (SomeInt 142436))
                                        (Build_Request MethodGet
                                                       a!4
                                                       a!1
                                                       (SomeInt 110606))
                                        (Build_Request MethodGet
                                                       a!5
                                                       a!1
                                                       (SomeInt 115468))))
                                 (a!9 (Build_ResponseHeaders
                                        (SomeContentType ContentTypeHTML)
                                        NoneSetCookie
                                        (SomeOrigin (OpaqueOrigin 34901))
                                        NoneURL
                                        a!8
                                        NoneReferrerPolicy))
                                 (a!19 (Build_Response (Build_URL ProtocolHTTP
                                                                  NoneDomain
                                                                  (SomeInt 132419)
                                                                  (url_path_res (anypath 109884)))
                                                       ResponseOk
                                                       a!17
                                                       a!18))
                                 (a!32 (Build_Response a!3
                                                       ResponseOk
                                                       a!26
                                                       (SomeContentElement
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 0)
                                                           a!31))))
                                 (a!38 (Build_Document 6
                                                       2
                                                       a!26
                                                       a!31
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!37)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!39 (SomeDOMElement (DOMElementResource
                                                         a!3
                                                         (ContentElementFrame
                                                           (Build_Frame a!3 0)
                                                           a!31))))
                                 (a!45 (Build_Document 12
                                                       2
                                                       a!26
                                                       a!31
                                                       (Build_DOM 2
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!44
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!37)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!65 (SomeDOMElement (DOMElementResource
                                                         a!3
                                                         (ContentElementFrame
                                                           (Build_Frame a!3
                                                                        34903)
                                                           a!31)))))
                           (let ((a!33 (Build_ArrayResponse
                                         (Build_Response a!4
                                                         ResponseOk
                                                         a!9
                                                         (SomeContentElement
                                                           (ContentElementHTML
                                                             a!13)))
                                         a!15
                                         a!19
                                         a!22
                                         a!25
                                         a!32))
                                 (a!43 (Build_Document 9
                                                       1
                                                       a!9
                                                       a!13
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!39
                                                                    a!40
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!41)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!42)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!46 (Build_Document 6
                                                       1
                                                       a!9
                                                       a!13
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!39
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!41)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!42)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!47 (Build_Document 3
                                                       1
                                                       a!9
                                                       a!13
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!41)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!42)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!53 (EvResponse (Build_Response a!4
                                                                   ResponseOk
                                                                   a!9
                                                                   (SomeContentElement
                                                                     (ContentElementHTML
                                                                       a!13)))
                                                   1))
                                 (a!66 (Build_Document 14
                                                       1
                                                       a!9
                                                       a!13
                                                       (Build_DOM 1
                                                                  0
                                                                  (Build_ArrayoptionDOMElement
                                                                    a!65
                                                                    a!40
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!41)
                                                                    NoneDOMElement
                                                                    (SomeDOMElement a!42)))
                                                       (Build_Initiators NoneInt
                                                                         (Build_ArrayoptionInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt
                                                                           NoneInt))))
                                 (a!71 (= (Build_Window 2
                                                        (SomeInt 3)
                                                        a!3
                                                        (SomeDomain (domain 10563))
                                                        a!45)
                                          a!69))
                                 (a!84 (= (Build_Window 2
                                                        (SomeInt 3)
                                                        a!3
                                                        (SomeDomain (domain 10563))
                                                        a!45)
                                          (Build_Window 2
                                                        (SomeInt 3)
                                                        a!3
                                                        (SomeDomain (domain 10563))
                                                        a!45)))
                                 (a!94 (wd_document (Build_Window 2
                                                                  (SomeInt 3)
                                                                  a!3
                                                                  (SomeDomain (domain 10563))
                                                                  a!45)))
                                 (a!102 (wd_location (Build_Window 2
                                                                   (SomeInt 3)
                                                                   a!3
                                                                   (SomeDomain (domain 10563))
                                                                   a!45))))
                           (let ((a!48 (Build_ArrayWindow
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!3
                                                       NoneDomain
                                                       a!38)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!43)
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!3
                                                       NoneDomain
                                                       a!45)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!46)
                                         (Build_Window 1
                                                       NoneInt
                                                       a!4
                                                       NoneDomain
                                                       a!47)
                                         (Build_Window 2
                                                       (SomeInt 3)
                                                       a!3
                                                       (SomeDomain (domain 10563))
                                                       a!45)))
                                 (a!55 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!3
                                                                            a!1
                                                                            (SomeInt 132535))
                                                             2)
                                                  (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                                   DOMTopLevel))
                                                             (consEvent a!53
                                                                        a!54))))
                                 (a!67 (Build_State 15
                                                    (Build_FetchEngine
                                                      11
                                                      EmitterClient
                                                      a!2
                                                      4
                                                      (SomeResponse a!22)
                                                      a!64)
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
                                                                  (SomeDomain (domain 10563))
                                                                  a!66)
                                                    (Build_ArrayoptionSetCookie
                                                      (SomeSetCookie a!52)
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
                                 (a!73 (wd_document (Build_Window 1
                                                                  NoneInt
                                                                  a!4
                                                                  (SomeDomain (domain 10563))
                                                                  a!66)))
                                 (a!95 (ite (= 0 4)
                                            (@4ArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))
                                            (@defaultArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))))
                                 (a!103 (not (= (sc_reg_domain a!52)
                                                (@0SomeDomain (url_host a!102))))))
                           (let ((a!51 (Build_Global a!6
                                                     a!33
                                                     (Build_ArrayInt 109034
                                                                     109035
                                                                     109036
                                                                     109037
                                                                     0
                                                                     1)
                                                     (Build_ArrayEmitter
                                                       a!34
                                                       EmitterClient
                                                       EmitterClient
                                                       EmitterClient
                                                       a!35
                                                       a!36)
                                                     a!48
                                                     a!49
                                                     (Build_ArrayprodOriginoptionCSP
                                                       a!50
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 119961)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 116433)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 145310)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 146579)
                                                         NoneCSP)
                                                       (pairOriginoptionCSP
                                                         (OpaqueOrigin 112760)
                                                         NoneCSP))
                                                     (Build_Config false
                                                                   false
                                                                   true
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   false
                                                                   true
                                                                   false)))
                                 (a!56 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                        (DOMIndex 0)))
                                                  (consEvent (EvResponse a!32 2)
                                                             a!55)))
                                 (a!74 (ite (= 0 4)
                                            (@4ArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))
                                            (@defaultArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))))
                                 (a!91 (= (st_window a!67)
                                          (Build_Window 1
                                                        NoneInt
                                                        a!4
                                                        (SomeDomain (domain 10563))
                                                        a!66)))
                                 (a!96 (ite (= 0 3)
                                            (@3ArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))
                                            a!95)))
                           (let ((a!57 (consEvent (EvRequest EmitterClient
                                                             (Build_Request MethodGet
                                                                            a!5
                                                                            a!1
                                                                            (SomeInt 115468))
                                                             3)
                                                  a!56))
                                 (a!72 (and (= a!69 a!70)
                                            a!71
                                            (= (st_window a!67) a!70)
                                            (= B (DOMPath nilInt DOMTopLevel))
                                            (= (DOMPath (consInt 0 nilInt)
                                                        (DOMIndex 0))
                                               B)
                                            (= a!51 A)))
                                 (a!75 (ite (= 0 3)
                                            (@3ArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))
                                            a!74))
                                 (a!85 (ite (= (frame_window (Build_Frame a!3
                                                                          34903))
                                               4)
                                            (@4ArrayWindow (windows a!51))
                                            (@defaultArrayWindow (windows a!51))))
                                 (a!97 (ite (= 0 2)
                                            (@2ArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))
                                            a!96)))
                           (let ((a!58 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                        (DOMIndex 1)))
                                                  (consEvent (EvResponse a!15 3)
                                                             a!57)))
                                 (a!76 (ite (= 0 2)
                                            (@2ArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))
                                            a!75))
                                 (a!86 (ite (= (frame_window (Build_Frame a!3
                                                                          34903))
                                               3)
                                            (@3ArrayWindow (windows a!51))
                                            a!85))
                                 (a!98 (ite (= 0 1)
                                            (@1ArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))
                                            a!97)))
                           (let ((a!59 (consEvent (EvResponse a!22 4)
                                                  (consEvent (EvRequest EmitterClient
                                                                        a!2
                                                                        4)
                                                             a!58)))
                                 (a!77 (ite (= 0 1)
                                            (@1ArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))
                                            a!76))
                                 (a!87 (ite (= (frame_window (Build_Frame a!3
                                                                          34903))
                                               2)
                                            (@2ArrayWindow (windows a!51))
                                            a!86))
                                 (a!99 (ite (= 0 0)
                                            (@0ArrayoptionDOMElement
                                              (dm_body (dc_dom a!94)))
                                            a!98)))
                           (let ((a!60 (consEvent (EvDOMUpdate (DOMPath (consInt 0
                                                                                 nilInt)
                                                                        (DOMIndex 0)))
                                                  a!59))
                                 (a!78 (ite (= 0 0)
                                            (@0ArrayoptionDOMElement
                                              (dm_body (dc_dom a!73)))
                                            a!77))
                                 (a!88 (ite (= (frame_window (Build_Frame a!3
                                                                          34903))
                                               1)
                                            (@1ArrayWindow (windows a!51))
                                            a!87))
                                 (a!100 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!99)))))
                                 (a!101 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!99))))))
                           (let ((a!61 (consEvent (EvScriptDomainRelaxation
                                                    (DOMPath nilInt
                                                             (DOMIndex 1))
                                                    (domain 10563))
                                                  a!60))
                                 (a!79 (= (@0ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!78)))
                                          (Build_Frame a!3 34903)))
                                 (a!80 (= (@1ContentElementFrame
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!78)))
                                          a!31))
                                 (a!81 (not ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!78)))))
                                 (a!82 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!78)))))
                                 (a!83 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!78)))))
                                 (a!89 (ite (= (frame_window (Build_Frame a!3
                                                                          34903))
                                               0)
                                            (@0ArrayWindow (windows a!51))
                                            a!88)))
                           (let ((a!62 (consEvent (EvScriptDomainRelaxation
                                                    (DOMPath (consInt 0 nilInt)
                                                             (DOMIndex 0))
                                                    (domain 10563))
                                                  a!61))
                                 (a!90 (= a!89
                                          (Build_Window 2
                                                        (SomeInt 3)
                                                        a!3
                                                        (SomeDomain (domain 10563))
                                                        a!45))))
                           (let ((a!63 (consEvent (EvScriptSetCookie
                                                    (DOMPath (consInt 0 nilInt)
                                                             (DOMIndex 0))
                                                    (DOMPath nilInt DOMTopLevel)
                                                    0
                                                    a!52)
                                                  a!62))
                                 (a!93 (and a!79
                                            a!80
                                            a!81
                                            a!82
                                            a!83
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!78)))
                                            ((_ is SomeDOMElement) a!78)
                                            a!84
                                            a!84
                                            a!84
                                            a!84
                                            a!90
                                            a!91
                                            (= (DOMPath nilInt (DOMIndex 0))
                                               (DOMPath nilInt (DOMIndex 0)))
                                            (= (DOMPath nilInt (DOMIndex 0))
                                               (DOMPath nilInt (DOMIndex 0)))
                                            a!92
                                            a!92
                                            (= a!51 a!51)
                                            (= a!51 a!51))))
                           (let ((a!104 (and (Reachable a!51 a!63 a!67)
                                             ((_ is Host) (sc_name a!52))
                                             (or a!72 a!93)
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!99)))
                                             a!100
                                             a!101
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!99)))
                                             ((_ is SomeDOMElement) a!99)
                                             ((_ is SomeDomain)
                                               (url_host a!102))
                                             a!103
                                             (= a!63 a!63)
                                             (= a!63 a!63))))
                             (=> a!104 (query!0 a!67 a!63 a!51))))))))))))))))
                           :weight 0))))
      (a!5 (Build_Request MethodGet
                          (Build_URL ProtocolData
                                     NoneDomain
                                     NoneInt
                                     (url_path_data 10 1))
                          a!4
                          (SomeInt 141637)))
      (a!11 (SomeCSP (Build_CSP a!10
                                (SomeTrustedTypes (Build_TrustedTypes
                                                    NoneoptionInt
                                                    false)))))
      (a!16 (Build_HTML 34900
                        34899
                        (Build_ArrayoptionHTMLElement
                          (SomeHTMLElement (HTMLFrame a!6))
                          (SomeHTMLElement (HTMLScript a!8))
                          a!13
                          a!14
                          NoneHTMLElement
                          a!15)))
      (a!18 (Build_Response a!8
                            ResponseOk
                            (Build_ResponseHeaders
                              (SomeContentType ContentTypeScript)
                              NoneSetCookie
                              (SomeOrigin (OpaqueOrigin 72864))
                              NoneURL
                              (SomeCSP a!17)
                              NoneReferrerPolicy)
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!8 8)))))
      (a!20 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 149824)
                                              109770
                                              NoneDomain
                                              (domain 148848)
                                              slash
                                              false
                                              false
                                              SSStrict))
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 148975)
                                  (url_path_data 150105 150106)))
              a!19
              NoneReferrerPolicy))
      (a!25 (Build_Response (Build_URL ProtocolData
                                       NoneDomain
                                       NoneInt
                                       (url_path_data 10 1))
                            ResponseOk
                            (Build_ResponseHeaders
                              (SomeContentType ContentTypeScript)
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              (SomeCSP a!23)
                              NoneReferrerPolicy)
                            (SomeContentElement a!24)))
      (a!28 (Build_Response (Build_URL ProtocolHTTP
                                       (SomeDomain (domain 148287))
                                       (SomeInt 135246)
                                       (url_path_data 123291 123292))
                            ResponseOk
                            a!26
                            a!27))
      (a!34 (Build_HTML 34881
                        34880
                        (Build_ArrayoptionHTMLElement
                          a!30
                          NoneHTMLElement
                          NoneHTMLElement
                          a!31
                          a!32
                          a!33)))
      (a!43 (SomeDOMElement (DOMElementResource
                              a!8
                              (ContentElementScript (Build_Script a!8 8)))))
      (a!47 (SomeDOMElement (DOMElementResource
                              (Build_URL ProtocolData
                                         NoneDomain
                                         NoneInt
                                         (url_path_data 10 1))
                              a!24)))
      (a!52 (Build_ArrayContentElement
              (ContentElementHTML
                (Build_HTML 112476
                            112477
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              a!24
              (ContentElementHTML
                (Build_HTML 111288
                            111289
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 111218
                            111219
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 129042
                            129043
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 125128
                            125129
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!56 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!7
                                                 a!4
                                                 (SomeInt 110606))
                                  1)
                       nilEvent))
      (a!104 (Build_State 1
                          (Build_FetchEngine
                            1
                            EmitterClient
                            (Build_Request MethodGet a!7 a!4 (SomeInt 110606))
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
                            a!4
                            NoneInt)))
(let ((a!9 (Build_ArrayRequest
             a!5
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 123989)
                                       (url_path_res slash))
                            a!4
                            (SomeInt 120694))
             (Build_Request MethodGet a!6 a!4 (SomeInt 132535))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 110500)
                                       (url_path_data 4572 109769))
                            a!4
                            (SomeInt 142436))
             (Build_Request MethodGet a!7 a!4 (SomeInt 110606))
             (Build_Request MethodGet a!8 a!4 (SomeInt 115468))))
      (a!12 (Build_ResponseHeaders
              (SomeContentType ContentTypeHTML)
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 34901))
              NoneURL
              a!11
              NoneReferrerPolicy))
      (a!22 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 132419)
                                       (url_path_res (anypath 109884)))
                            ResponseOk
                            a!20
                            a!21))
      (a!35 (Build_Response a!6
                            ResponseOk
                            a!29
                            (SomeContentElement
                              (ContentElementFrame (Build_Frame a!6 0) a!34))))
      (a!41 (Build_Document 6
                            2
                            a!29
                            a!34
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!40)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!42 (SomeDOMElement (DOMElementResource
                              a!6
                              (ContentElementFrame (Build_Frame a!6 0) a!34))))
      (a!48 (Build_Document 12
                            2
                            a!29
                            a!34
                            (Build_DOM 2
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!47
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!40)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!66 (SomeDOMElement (DOMElementResource
                              a!6
                              (ContentElementFrame (Build_Frame a!6 34903) a!34))))
      (a!73 (SomeDOMElement (DOMElementResource
                              (Build_URL ProtocolData
                                         NoneDomain
                                         NoneInt
                                         (url_path_data 10 1))
                              (ContentElementFrame (Build_Frame a!6 2) a!34))))
      (a!85 (Build_FetchEngine
              8
              EmitterClient
              (Build_Request MethodGet a!8 a!4 (SomeInt 115468))
              3
              (SomeResponse a!18)
              a!82))
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
(let ((a!36 (Build_ArrayResponse
              (Build_Response a!7
                              ResponseOk
                              a!12
                              (SomeContentElement (ContentElementHTML a!16)))
              a!18
              a!22
              a!25
              a!28
              a!35))
      (a!46 (Build_Document 9
                            1
                            a!12
                            a!16
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!42
                                         a!43
                                         NoneDOMElement
                                         (SomeDOMElement a!44)
                                         NoneDOMElement
                                         (SomeDOMElement a!45)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!49 (Build_Document 6
                            1
                            a!12
                            a!16
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!42
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!44)
                                         NoneDOMElement
                                         (SomeDOMElement a!45)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!50 (Build_Document 3
                            1
                            a!12
                            a!16
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!44)
                                         NoneDOMElement
                                         (SomeDOMElement a!45)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!55 (EvResponse (Build_Response a!7
                                        ResponseOk
                                        a!12
                                        (SomeContentElement
                                          (ContentElementHTML a!16)))
                        1))
      (a!67 (Build_Document 14
                            1
                            a!12
                            a!16
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!66
                                         a!43
                                         NoneDOMElement
                                         (SomeDOMElement a!44)
                                         NoneDOMElement
                                         (SomeDOMElement a!45)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!74 (Build_Document 12
                            1
                            a!12
                            a!16
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         a!73
                                         a!43
                                         NoneDOMElement
                                         (SomeDOMElement a!44)
                                         NoneDOMElement
                                         (SomeDOMElement a!45)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!92 (Build_FetchEngine
              5
              EmitterClient
              (Build_Request MethodGet a!6 a!4 (SomeInt 132535))
              2
              (SomeResponse a!35)
              a!89))
      (a!98 (SomeResponse (Build_Response a!7
                                          ResponseOk
                                          a!12
                                          (SomeContentElement
                                            (ContentElementHTML a!16))))))
(let ((a!51 (Build_ArrayWindow
              (Build_Window 2 (SomeInt 3) a!6 NoneDomain a!41)
              (Build_Window 1 NoneInt a!7 NoneDomain a!46)
              (Build_Window 2 (SomeInt 3) a!6 NoneDomain a!48)
              (Build_Window 1 NoneInt a!7 NoneDomain a!49)
              (Build_Window 1 NoneInt a!7 NoneDomain a!50)
              (Build_Window 2 (SomeInt 3) a!6 (SomeDomain (domain 10563)) a!48)))
      (a!57 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!6
                                                 a!4
                                                 (SomeInt 132535))
                                  2)
                       (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                  (consEvent a!55 a!56))))
      (a!68 (Build_State 14
                         (Build_FetchEngine
                           11
                           EmitterClient
                           a!5
                           4
                           (SomeResponse a!25)
                           a!65)
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
                                       a!7
                                       (SomeDomain (domain 10563))
                                       a!67)
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
      (a!70 (Build_State 15
                         (Build_FetchEngine
                           11
                           EmitterClient
                           a!5
                           4
                           (SomeResponse a!25)
                           a!65)
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
                                       a!7
                                       (SomeDomain (domain 10563))
                                       a!67)
                         (Build_ArrayoptionSetCookie
                           (SomeSetCookie a!69)
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
      (a!75 (Build_State 13
                         (Build_FetchEngine
                           11
                           EmitterClient
                           a!5
                           4
                           (SomeResponse a!25)
                           a!65)
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
                                       a!7
                                       (SomeDomain (domain 10563))
                                       a!74)
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
      (a!90 (Build_State 7
                         (Build_FetchEngine
                           7
                           EmitterClient
                           (Build_Request MethodGet a!8 a!4 (SomeInt 115468))
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
                         (Build_Window 1 NoneInt a!7 NoneDomain a!49)
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
      (a!97 (Build_State 4
                         (Build_FetchEngine
                           4
                           EmitterClient
                           (Build_Request MethodGet a!6 a!4 (SomeInt 132535))
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
                         (Build_Window 1 NoneInt a!7 NoneDomain a!50)
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
      (a!99 (Build_FetchEngine
              2
              EmitterClient
              (Build_Request MethodGet a!7 a!4 (SomeInt 110606))
              1
              a!98
              a!96)))
(let ((a!54 (Build_Global a!9
                          a!36
                          (Build_ArrayInt 109034 109035 109036 109037 0 1)
                          (Build_ArrayEmitter
                            a!37
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            a!38
                            a!39)
                          a!51
                          a!52
                          (Build_ArrayprodOriginoptionCSP
                            a!53
                            (pairOriginoptionCSP (OpaqueOrigin 119961) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 116433) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 145310) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 146579) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 112760) NoneCSP))
                          (Build_Config false
                                        false
                                        true
                                        false
                                        false
                                        false
                                        false
                                        false
                                        false
                                        false
                                        true
                                        false)))
      (a!58 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 0)))
                       (consEvent (EvResponse a!35 2) a!57))))
(let ((a!59 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!8
                                                 a!4
                                                 (SomeInt 115468))
                                  3)
                       a!58))
      (a!93 (Reachable a!54
                       a!58
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
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!49)
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
      (a!94 (Reachable a!54
                       (consEvent (EvResponse a!35 2) a!57)
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
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!50)
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
      (a!100 (Reachable a!54
                        (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                   (consEvent a!55 a!56))
                        (Build_State 3
                                     a!99
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
                                                   a!7
                                                   NoneDomain
                                                   a!50)
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
      (a!103 (Reachable a!54
                        (consEvent a!55 a!56)
                        (Build_State 2
                                     a!99
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
                                       NoneStorageItem)))))
(let ((a!60 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 1)))
                       (consEvent (EvResponse a!18 3) a!59)))
      (a!88 (Reachable a!54
                       (consEvent (EvResponse a!18 3) a!59)
                       (Build_State 8
                                    a!85
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!49)
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
                                      NoneStorageItem)))))
(let ((a!61 (consEvent (EvResponse a!25 4)
                       (consEvent (EvRequest EmitterClient a!5 4) a!60)))
      (a!83 (Reachable a!54
                       (consEvent (EvRequest EmitterClient a!5 4) a!60)
                       (Build_State 10
                                    (Build_FetchEngine
                                      10
                                      EmitterClient
                                      a!5
                                      4
                                      NoneResponse
                                      a!82)
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!46)
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
      (a!86 (Reachable a!54
                       a!60
                       (Build_State 9
                                    a!85
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!46)
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
                                      NoneStorageItem)))))
(let ((a!62 (consEvent (EvDOMUpdate (DOMPath (consInt 0 nilInt) (DOMIndex 0)))
                       a!61))
      (a!79 (Reachable a!54
                       a!61
                       (Build_State 11
                                    (Build_FetchEngine
                                      11
                                      EmitterClient
                                      a!5
                                      4
                                      (SomeResponse a!25)
                                      a!65)
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!46)
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
                                      NoneStorageItem)))))
(let ((a!63 (consEvent (EvScriptDomainRelaxation
                         (DOMPath nilInt (DOMIndex 1))
                         (domain 10563))
                       a!62))
      (a!77 (Reachable a!54
                       a!62
                       (Build_State 12
                                    (Build_FetchEngine
                                      11
                                      EmitterClient
                                      a!5
                                      4
                                      (SomeResponse a!25)
                                      a!65)
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!7 NoneDomain a!74)
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
                                      NoneStorageItem)))))
(let ((a!64 (consEvent (EvScriptDomainRelaxation
                         (DOMPath (consInt 0 nilInt) (DOMIndex 0))
                         (domain 10563))
                       a!63)))
(let ((a!71 (consEvent (EvScriptSetCookie
                         (DOMPath (consInt 0 nilInt) (DOMIndex 0))
                         (DOMPath nilInt DOMTopLevel)
                         0
                         a!69)
                       a!64)))
(let ((a!76 (hyper-res (hyper-res a!2
                                  a!3
                                  (=> (Reachable a!54 a!64 a!68)
                                      (query!0 a!70 a!71 a!54)))
                       a!72
                       (=> (Reachable a!54 a!63 a!75) (query!0 a!70 a!71 a!54)))))
(let ((a!80 (hyper-res (hyper-res a!76 a!72 (=> a!77 (query!0 a!70 a!71 a!54)))
                       a!78
                       (=> a!79 (query!0 a!70 a!71 a!54)))))
(let ((a!87 (hyper-res (hyper-res a!80 a!81 (=> a!83 (query!0 a!70 a!71 a!54)))
                       a!84
                       (=> a!86 (query!0 a!70 a!71 a!54)))))
(let ((a!91 (hyper-res (hyper-res a!87 a!78 (=> a!88 (query!0 a!70 a!71 a!54)))
                       a!81
                       (=> (Reachable a!54 a!59 a!90) (query!0 a!70 a!71 a!54)))))
(let ((a!95 (hyper-res (hyper-res a!91 a!84 (=> a!93 (query!0 a!70 a!71 a!54)))
                       a!78
                       (=> a!94 (query!0 a!70 a!71 a!54)))))
(let ((a!101 (hyper-res (hyper-res a!95
                                   a!81
                                   (=> (Reachable a!54 a!57 a!97)
                                       (query!0 a!70 a!71 a!54)))
                        a!84
                        (=> a!100 (query!0 a!70 a!71 a!54)))))
(let ((a!105 (hyper-res (hyper-res a!101
                                   a!78
                                   (=> a!103 (query!0 a!70 a!71 a!54)))
                        a!81
                        (=> (Reachable a!54 a!56 a!104)
                            (query!0 a!70 a!71 a!54)))))
  (hyper-res (hyper-res a!105
                        a!84
                        (=> (Reachable a!54 nilEvent a!107)
                            (query!0 a!70 a!71 a!54)))
             a!108
             (query!0 a!70 a!71 a!54))))))))))))))))))))))
