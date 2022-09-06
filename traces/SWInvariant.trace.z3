
(let ((a!1 (asserted (forall ((A Int)
                              (B Request)
                              (C Int)
                              (D Int)
                              (E Response)
                              (F Int)
                              (G Response)
                              (H Int)
                              (I Request)
                              (J Request)
                              (K Global)
                              (L listEvent)
                              (M State))
                       (! (let ((a!1 (ite (= A 4)
                                          (@4ArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))
                                          (@defaultArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))))
                                (a!7 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      DOMTopLevel))
                                                (consEvent (EvResponse G H)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 I
                                                                                 H)
                                                                      nilEvent)))))
                          (let ((a!2 (ite (= A 3)
                                          (@3ArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))
                                          a!1))
                                (a!8 (consEvent (EvDOMUpdate (DOMPath nilInt
                                                                      (DOMIndex 3)))
                                                (consEvent (EvResponse E F)
                                                           (consEvent (EvRequest EmitterClient
                                                                                 J
                                                                                 F)
                                                                      a!7)))))
                          (let ((a!3 (ite (= A 2)
                                          (@2ArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))
                                          a!2)))
                          (let ((a!4 (ite (= A 1)
                                          (@1ArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))
                                          a!3)))
                          (let ((a!5 (ite (= A 0)
                                          (@0ArrayoptionprodprodEmitterIntInt
                                            (ft_history (st_fetch_engine M)))
                                          a!4)))
                          (let ((a!6 (EvScriptUpdateCache
                                       (DOMPath nilInt (DOMIndex 3))
                                       (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                           (@0SomeprodprodEmitterIntInt
                                                             a!5)))
                                       (SomeInt D)))
                                (a!10 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                             (@0SomeprodprodEmitterIntInt
                                                               a!5)))
                                         0))
                                (a!11 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                             (@0SomeprodprodEmitterIntInt
                                                               a!5)))
                                         1))
                                (a!12 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                             (@0SomeprodprodEmitterIntInt
                                                               a!5)))
                                         2))
                                (a!13 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                             (@0SomeprodprodEmitterIntInt
                                                               a!5)))
                                         3))
                                (a!14 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                                             (@0SomeprodprodEmitterIntInt
                                                               a!5)))
                                         4))
                                (a!25 (ite (= (@1pairprodEmitterIntInt
                                                (@0SomeprodprodEmitterIntInt
                                                  a!5))
                                              4)
                                           (@4ArrayResponse (responses K))
                                           (@defaultArrayResponse (responses K)))))
                          (let ((a!9 (= L
                                        (consEvent (EvWorkerCacheMatch D)
                                                   (consEvent (EvRequest EmitterClient
                                                                         B
                                                                         C)
                                                              (consEvent a!6
                                                                         a!8)))))
                                (a!15 (ite a!13
                                           (@3ArrayInt (server_responses K))
                                           (ite a!14
                                                (@4ArrayInt (server_responses K))
                                                (@defaultArrayInt (server_responses K)))))
                                (a!26 (ite (= (@1pairprodEmitterIntInt
                                                (@0SomeprodprodEmitterIntInt
                                                  a!5))
                                              3)
                                           (@3ArrayResponse (responses K))
                                           a!25))
                                (a!31 (ite a!13
                                           (@3ArrayRequest (requests K))
                                           (ite a!14
                                                (@4ArrayRequest (requests K))
                                                (@defaultArrayRequest
                                                  (requests K))))))
                          (let ((a!16 (ite a!11
                                           (@1ArrayInt (server_responses K))
                                           (ite a!12
                                                (@2ArrayInt (server_responses K))
                                                a!15)))
                                (a!27 (ite (= (@1pairprodEmitterIntInt
                                                (@0SomeprodprodEmitterIntInt
                                                  a!5))
                                              2)
                                           (@2ArrayResponse (responses K))
                                           a!26))
                                (a!32 (ite a!11
                                           (@1ArrayRequest (requests K))
                                           (ite a!12
                                                (@2ArrayRequest (requests K))
                                                a!31))))
                          (let ((a!17 (= (ite a!10
                                              (@0ArrayInt (server_responses K))
                                              a!16)
                                         0))
                                (a!18 (= (ite a!10
                                              (@0ArrayInt (server_responses K))
                                              a!16)
                                         1))
                                (a!19 (= (ite a!10
                                              (@0ArrayInt (server_responses K))
                                              a!16)
                                         2))
                                (a!20 (= (ite a!10
                                              (@0ArrayInt (server_responses K))
                                              a!16)
                                         3))
                                (a!21 (= (ite a!10
                                              (@0ArrayInt (server_responses K))
                                              a!16)
                                         4))
                                (a!28 (ite (= (@1pairprodEmitterIntInt
                                                (@0SomeprodprodEmitterIntInt
                                                  a!5))
                                              1)
                                           (@1ArrayResponse (responses K))
                                           a!27))
                                (a!33 (rq_url (ite a!10
                                                   (@0ArrayRequest (requests K))
                                                   a!32))))
                          (let ((a!22 (ite a!20
                                           (@3ArrayResponse (responses K))
                                           (ite a!21
                                                (@4ArrayResponse (responses K))
                                                (@defaultArrayResponse
                                                  (responses K)))))
                                (a!29 (ite (= (@1pairprodEmitterIntInt
                                                (@0SomeprodprodEmitterIntInt
                                                  a!5))
                                              0)
                                           (@0ArrayResponse (responses K))
                                           a!28)))
                          (let ((a!23 (ite a!18
                                           (@1ArrayResponse (responses K))
                                           (ite a!19
                                                (@2ArrayResponse (responses K))
                                                a!22))))
                          (let ((a!24 (rp_headers (ite a!17
                                                       (@0ArrayResponse (responses K))
                                                       a!23))))
                          (let ((a!30 (not (= (rp_hd_csp a!24)
                                              (rp_hd_csp (rp_headers a!29))))))
                          (let ((a!34 (and (Reachable K L M)
                                           ((_ is pairprodEmitterIntInt)
                                             (@0SomeprodprodEmitterIntInt a!5))
                                           ((_ is SomeprodprodEmitterIntInt)
                                             a!5)
                                           a!9
                                           a!30
                                           (not (= (rq_url I) (rq_url J)))
                                           (not (c_worker_allow_synthetic_responses
                                                  (config K)))
                                           (or ((_ is ProtocolHTTPS)
                                                 (url_protocol a!33))
                                               ((_ is ProtocolHTTP)
                                                 (url_protocol a!33)))
                                           ((_ is pairEmitterInt)
                                             (@0pairprodEmitterIntInt
                                               (@0SomeprodprodEmitterIntInt a!5))))))
                            (=> a!34 (query!0 M L K))))))))))))))))
                          :weight 0))))
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
      (a!3 (Build_URL ProtocolHTTP
                      (SomeDomain (subdomain 1970 1971))
                      (SomeInt 4756)
                      (url_path_res (anypath 5001))))
      (a!4 (Build_URL ProtocolHTTPS
                      (SomeDomain (subdomain 571 572))
                      (SomeInt 4754)
                      (url_path_res slash)))
      (a!5 (Build_URL ProtocolHTTPS
                      (SomeDomain (subdomain 571 572))
                      (SomeInt 4754)
                      (url_path_res (anypath 38))))
      (a!7 (SomeCSP (Build_CSP (SomeCSPSrc (CSPSrcScheme ProtocolHTTP))
                               (SomeTrustedTypes (Build_TrustedTypes
                                                   NoneoptionInt
                                                   false)))))
      (a!9 (SomeHTMLElement (HTMLForm MethodGet
                                      (Build_URL ProtocolHTTP
                                                 NoneDomain
                                                 (SomeInt 9289)
                                                 (url_path_data 10857 10858)))))
      (a!10 (SomeHTMLElement (HTMLFrame (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 9446)
                                                   (url_path_data 7593 7594)))))
      (a!11 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 15662)
                                                  (url_path_data 11529 11530)))))
      (a!12 (SomeHTMLElement (HTMLForm MethodGet
                                       (Build_URL ProtocolHTTP
                                                  NoneDomain
                                                  (SomeInt 7718)
                                                  (url_path_data 9837 9838)))))
      (a!14 (Build_ResponseHeaders
              NoneContentType
              NoneSetCookie
              (SomeOrigin (OpaqueOrigin 12681))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 17076)
                                  (url_path_data 16771 16772)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!15 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 16856
                            16857
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!16 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 17084)
                                              5588
                                              NoneDomain
                                              (domain 16460)
                                              slash
                                              false
                                              false
                                              SSStrict))
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 17409)
                                  (url_path_data 16340 16341)))
              NoneCSP
              NoneReferrerPolicy))
      (a!17 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 17177
                            17178
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!19 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 16000)
                                              5589
                                              NoneDomain
                                              (domain 16369)
                                              slash
                                              false
                                              false
                                              SSStrict))
              (SomeOrigin (OpaqueOrigin 13938))
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 16878)
                                  (url_path_data 16515 16516)))
              (SomeCSP (Build_CSP NoneCSPSrc NoneTrustedTypes))
              NoneReferrerPolicy))
      (a!20 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 17261
                            17262
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!22 (SomeSetCookie (Build_SetCookie (NoPrefix 4757)
                                            3320
                                            (SomeDomain (subdomain 1970 1971))
                                            (subdomain 1970 1971)
                                            (anypath 5341)
                                            false
                                            false
                                            SSStrict)))
      (a!23 (SomeCSP (Build_CSP (SomeCSPSrc CSPSrcNone)
                                (SomeTrustedTypes (Build_TrustedTypes
                                                    NoneoptionInt
                                                    false)))))
      (a!25 (Build_ResponseHeaders
              NoneContentType
              (SomeSetCookie (Build_SetCookie (NoPrefix 16293)
                                              5590
                                              NoneDomain
                                              (domain 16180)
                                              slash
                                              false
                                              false
                                              SSStrict))
              NoneOrigin
              (SomeURL (Build_URL ProtocolHTTP
                                  NoneDomain
                                  (SomeInt 15723)
                                  (url_path_data 16662 16663)))
              NoneCSP
              NoneReferrerPolicy))
      (a!26 (SomeContentElement
              (ContentElementHTML
                (Build_HTML 16625
                            16626
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!28 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 19226)
                                                    (url_path_data 18439 18440))
                                         17399)))
      (a!29 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 18490)
                                                    (url_path_data 19804 19805))
                                         16436)))
      (a!30 (EmitterScript (DOMPath nilInt DOMTopLevel)
                           (Build_Script (Build_URL ProtocolHTTP
                                                    NoneDomain
                                                    (SomeInt 19636)
                                                    (url_path_data 19393 19394))
                                         17249)))
      (a!31 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 9289)
                                                   (url_path_data 10857 10858)))))
      (a!33 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 15662)
                                                   (url_path_data 11529 11530)))))
      (a!34 (DOMElementForm (Build_Form MethodGet
                                        (Build_URL ProtocolHTTP
                                                   NoneDomain
                                                   (SomeInt 7718)
                                                   (url_path_data 9837 9838)))))
      (a!36 (Build_Document 3765
                            3766
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 3761
                                        3762
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 3763
                                       3764
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 8954)
                                              (Build_ArrayoptionInt
                                                (SomeInt 12122)
                                                (SomeInt 15655)
                                                (SomeInt 10636)
                                                (SomeInt 15499)
                                                (SomeInt 15588)
                                                (SomeInt 9984)))))
      (a!37 (Build_Document 3772
                            3773
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 3768
                                        3769
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 3770
                                       3771
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 13918)
                                              (Build_ArrayoptionInt
                                                (SomeInt 7708)
                                                (SomeInt 8597)
                                                (SomeInt 15183)
                                                (SomeInt 7304)
                                                (SomeInt 5814)
                                                (SomeInt 10482)))))
      (a!39 (Build_Document 3779
                            3780
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              NoneCSP
                              NoneReferrerPolicy)
                            (Build_HTML 3775
                                        3776
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 3777
                                       3778
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 6661)
                                              (Build_ArrayoptionInt
                                                (SomeInt 13701)
                                                (SomeInt 11630)
                                                (SomeInt 9506)
                                                (SomeInt 9590)
                                                (SomeInt 7683)
                                                (SomeInt 9784)))))
      (a!40 (SomeCSP (Build_CSP (SomeCSPSrc (CSPSrcScheme ProtocolHTTPS))
                                NoneTrustedTypes)))
      (a!43 (Build_ArrayContentElement
              (ContentElementHTML
                (Build_HTML 5945
                            5946
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 6214
                            6215
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 5780
                            5781
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 8621
                            8622
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 14978
                            14979
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))
              (ContentElementHTML
                (Build_HTML 5975
                            5976
                            (Build_ArrayoptionHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement
                              NoneHTMLElement)))))
      (a!44 (pairOriginoptionCSP
              (TupleOrigin ProtocolHTTP (SomeDomain (domain 0)) (SomeInt 0))
              NoneCSP))
      (a!52 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 540) 0))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 4))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 4) 1))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!53 (Build_ServiceWorker
              7
              (Build_ArrayoptionInt
                NoneInt
                NoneInt
                NoneInt
                NoneInt
                (SomeInt 1)
                NoneInt)))
      (a!89 (asserted (forall ((A State)
                               (B State)
                               (C listEvent)
                               (D Int)
                               (E FetchEngine)
                               (F Global)
                               (G Int)
                               (H listEvent)
                               (I Int)
                               (J FetchEngine)
                               (K ServiceWorker)
                               (L Window)
                               (M ArrayoptionSetCookie)
                               (N ArrayoptionBlob)
                               (O ArrayoptionStorageItem))
                        (! (let ((a!1 (ite (= G 3)
                                           (@3ArrayResponse (responses F))
                                           (ite (= G 4)
                                                (@4ArrayResponse (responses F))
                                                (@defaultArrayResponse
                                                  (responses F)))))
                                 (a!4 (SomeprodprodEmitterIntInt
                                        (pairprodEmitterIntInt
                                          (pairEmitterInt (ft_emitter E) D)
                                          G)))
                                 (a!10 (ite (= D 3)
                                            (@3ArrayoptionInt (wk_cache K))
                                            (ite (= D 4)
                                                 (@4ArrayoptionInt (wk_cache K))
                                                 (@defaultArrayoptionInt
                                                   (wk_cache K)))))
                                 (a!14 (ite (= D 3)
                                            (@3ArrayRequest (requests F))
                                            (ite (= D 4)
                                                 (@4ArrayRequest (requests F))
                                                 (@defaultArrayRequest
                                                   (requests F)))))
                                 (a!19 (or ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location L)))
                                           ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location L)))))
                                 (a!20 (SomeOrigin (TupleOrigin (url_protocol (wd_location L))
                                                                (url_host (wd_location L))
                                                                (url_port (wd_location L)))))
                                 (a!21 (OpaqueOrigin (@0url_path_data (url_path (wd_location L)))))
                                 (a!23 (SomeOrigin (@0url_path_blob (url_path (wd_location L)))))
                                 (a!30 ((_ is ProtocolHTTPS)
                                         (url_protocol (rq_url (ft_request E)))))
                                 (a!31 ((_ is ProtocolHTTP)
                                         (url_protocol (rq_url (ft_request E))))))
                           (let ((a!2 (ite (= G 1)
                                           (@1ArrayResponse (responses F))
                                           (ite (= G 2)
                                                (@2ArrayResponse (responses F))
                                                a!1)))
                                 (a!5 (ite (= (ft_correlator E) 4)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             a!4
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E)))
                                           (ft_history E)))
                                 (a!11 (ite (= D 1)
                                            (@1ArrayoptionInt (wk_cache K))
                                            (ite (= D 2)
                                                 (@2ArrayoptionInt (wk_cache K))
                                                 a!10)))
                                 (a!15 (ite (= D 1)
                                            (@1ArrayRequest (requests F))
                                            (ite (= D 2)
                                                 (@2ArrayRequest (requests F))
                                                 a!14)))
                                 (a!22 (ite ((_ is url_path_data)
                                              (url_path (wd_location L)))
                                            (SomeOrigin a!21)
                                            NoneOrigin))
                                 (a!24 (ite ((_ is url_path_blob)
                                              (url_path (wd_location L)))
                                            a!23
                                            NoneOrigin)))
                           (let ((a!3 (SomeResponse (ite (= G 0)
                                                         (@0ArrayResponse (responses F))
                                                         a!2)))
                                 (a!6 (ite (= (ft_correlator E) 3)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             a!4
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E)))
                                           a!5))
                                 (a!12 (= (ite (= D 0)
                                               (@0ArrayoptionInt (wk_cache K))
                                               a!11)
                                          (SomeInt G)))
                                 (a!13 (rp_url (ite (= G 0)
                                                    (@0ArrayResponse (responses F))
                                                    a!2)))
                                 (a!16 (= (ft_request E)
                                          (ite (= D 0)
                                               (@0ArrayRequest (requests F))
                                               a!15)))
                                 (a!17 (rp_content (ite (= G 0)
                                                        (@0ArrayResponse (responses F))
                                                        a!2)))
                                 (a!18 (rp_headers (ite (= G 0)
                                                        (@0ArrayResponse (responses F))
                                                        a!2)))
                                 (a!25 (ite ((_ is url_path_data)
                                              (url_path (wd_location L)))
                                            NoneOrigin
                                            a!24)))
                           (let ((a!7 (ite (= (ft_correlator E) 2)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             a!4
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E)))
                                           a!6))
                                 (a!26 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location L)))
                                            a!22
                                            a!25)))
                           (let ((a!8 (ite (= (ft_correlator E) 1)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             (@0ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             a!4
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E)))
                                           a!7))
                                 (a!27 (= (SomeOrigin (@0SomeOrigin (rp_hd_access_control_allow_origin
                                                                      a!18)))
                                          (ite a!19 a!20 a!26))))
                           (let ((a!9 (ite (= (ft_correlator E) 0)
                                           (Build_ArrayoptionprodprodEmitterIntInt
                                             a!4
                                             (@1ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@2ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@3ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@4ArrayoptionprodprodEmitterIntInt
                                               (ft_history E))
                                             (@defaultArrayoptionprodprodEmitterIntInt
                                               (ft_history E)))
                                           a!8))
                                 (a!28 (ite ((_ is EmitterScript)
                                              (ft_emitter E))
                                            (or (= a!17 NoneContentElement)
                                                a!27)
                                            (or ((_ is EmitterWorker)
                                                  (ft_emitter E))
                                                ((_ is EmitterForm)
                                                  (ft_emitter E))
                                                a!27))))
                           (let ((a!29 (or ((_ is EmitterClient) (ft_emitter E))
                                           a!28
                                           (not ((_ is SomeOrigin)
                                                  (rp_hd_access_control_allow_origin
                                                    a!18))))))
                           (let ((a!32 (and (Reachable F H A)
                                            (= A (Build_State I E K L M N O))
                                            (= B
                                               (Build_State (+ 1 I) J K L M N O))
                                            (= J
                                               (Build_FetchEngine
                                                 (+ 1 I)
                                                 (ft_emitter E)
                                                 (ft_request E)
                                                 (ft_correlator E)
                                                 a!3
                                                 a!9))
                                            a!12
                                            (= (ft_response E) NoneResponse)
                                            (= a!13 (rq_url (ft_request E)))
                                            a!16
                                            (not (= (ft_emitter E)
                                                    EmitterWorker))
                                            a!29
                                            (or a!30 a!31)
                                            (= C
                                               (consEvent (EvWorkerCacheMatch G)
                                                          H)))))
                             (=> a!32 (Reachable F C B))))))))))
                           :weight 0))))
      (a!90 (Build_ArrayoptionprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 540) 0))
              (SomeprodprodEmitterIntInt
                (pairprodEmitterIntInt (pairEmitterInt EmitterClient 1) 4))
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt
              NoneprodprodEmitterIntInt))
      (a!93 (asserted (forall ((A Script)
                               (B NestedDOMPath)
                               (C Window)
                               (D Global)
                               (E Global)
                               (F NestedDOMPath)
                               (G DOMSelector)
                               (H Window)
                               (I Window)
                               (J NestedDOMPath)
                               (K listInt)
                               (L Int)
                               (M Window)
                               (N Script)
                               (O Form)
                               (P NestedDOMPath)
                               (Q Window)
                               (R Global)
                               (S Global)
                               (T NestedDOMPath)
                               (U DOMSelector)
                               (V Window)
                               (W Window)
                               (X NestedDOMPath)
                               (Y listInt)
                               (Z Int)
                               (A1 Window)
                               (B1 Form)
                               (C1 Request)
                               (D1 Int)
                               (E1 Script)
                               (F1 NestedDOMPath)
                               (G1 Window)
                               (H1 Global)
                               (I1 Global)
                               (J1 NestedDOMPath)
                               (K1 DOMSelector)
                               (L1 Window)
                               (M1 Window)
                               (N1 NestedDOMPath)
                               (O1 listInt)
                               (P1 Int)
                               (Q1 Window)
                               (R1 Script)
                               (S1 Global)
                               (T1 Emitter)
                               (U1 Window)
                               (V1 Window)
                               (W1 State)
                               (X1 State)
                               (Y1 listEvent)
                               (Z1 URL)
                               (A2 NestedDOMPath)
                               (B2 Script)
                               (C2 NestedDOMPath)
                               (D2 Form)
                               (E2 URL)
                               (F2 Response)
                               (G2 Int)
                               (H2 Blob)
                               (I2 Origin)
                               (J2 FetchEngine)
                               (K2 Request)
                               (L2 listEvent)
                               (M2 Int)
                               (N2 ServiceWorker)
                               (O2 ArrayoptionSetCookie)
                               (P2 ArrayoptionBlob)
                               (Q2 ArrayoptionStorageItem))
                        (! (let ((a!1 (Build_State (+ 1 M2)
                                                   (Build_FetchEngine
                                                     (+ 1 M2)
                                                     T1
                                                     K2
                                                     (+ 1 (ft_correlator J2))
                                                     NoneResponse
                                                     (ft_history J2))
                                                   N2
                                                   U1
                                                   O2
                                                   P2
                                                   Q2))
                                 (a!2 (or ((_ is ProtocolHTTPS)
                                            (url_protocol (rq_url K2)))
                                          ((_ is ProtocolHTTP)
                                            (url_protocol (rq_url K2)))))
                                 (a!3 (not ((_ is url_path_blob)
                                             (url_path (rq_url K2)))))
                                 (a!4 (not ((_ is url_path_data)
                                             (url_path (rq_url K2)))))
                                 (a!6 (not ((_ is SomeInt)
                                             (url_port (rq_url K2)))))
                                 (a!7 (not ((_ is SomeDomain)
                                             (url_host (rq_url K2)))))
                                 (a!11 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!12 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!13 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!14 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!15 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!16 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document A1)))))
                                 (a!20 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!21 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!22 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!23 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!24 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!25 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document M)))))
                                 (a!32 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!33 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!34 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!35 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!36 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!37 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document Q1)))))
                                 (a!43 (ite (= D1 3)
                                            (@3ArrayEmitter (emitters S1))
                                            (ite (= D1 4)
                                                 (@4ArrayEmitter (emitters S1))
                                                 (@defaultArrayEmitter
                                                   (emitters S1)))))
                                 (a!47 (not (sc_secure (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                          O2)))))
                                 (a!49 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                           O2)))
                                          SSLax))
                                 (a!50 (= (sc_same_site (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                           O2)))
                                          SSNone))
                                 (a!52 ((_ is domain)
                                         (@0SomeDomain (url_host (wd_location V1)))))
                                 (a!53 ((_ is domain)
                                         (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                           O2)))))
                                 (a!54 (@0domain (@0SomeDomain (url_host (wd_location V1)))))
                                 (a!55 (@0domain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                   O2)))))
                                 (a!56 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                      O2)))))
                                 (a!57 (@1subdomain (@0SomeDomain (url_host (wd_location V1)))))
                                 (a!59 ((_ is SomeDomain)
                                         (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                       O2)))))
                                 (a!60 ((_ is domain)
                                         (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!61 (@0domain (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!62 (@0SomeDomain (sc_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                   O2)))))
                                 (a!63 (@1subdomain (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!64 (@0subdomain (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!68 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                            O2)))
                                          (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!70 ((_ is slash)
                                         (@0url_path_res (url_path (rq_url K2)))))
                                 (a!71 ((_ is slash)
                                         (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                     O2)))))
                                 (a!72 (@0anypath (@0url_path_res (url_path (rq_url K2)))))
                                 (a!73 (@0anypath (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                              O2)))))
                                 (a!75 (Build_CookieMapping
                                         (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                     O2)))
                                         (sc_value (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                      O2)))))
                                 (a!77 (not (sc_secure (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                          O2)))))
                                 (a!79 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                           O2)))
                                          SSLax))
                                 (a!80 (= (sc_same_site (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                           O2)))
                                          SSNone))
                                 (a!82 ((_ is domain)
                                         (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                           O2)))))
                                 (a!83 (@0domain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                   O2)))))
                                 (a!84 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                      O2)))))
                                 (a!86 ((_ is SomeDomain)
                                         (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                       O2)))))
                                 (a!87 (@0SomeDomain (sc_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                   O2)))))
                                 (a!91 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                            O2)))
                                          (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!93 ((_ is slash)
                                         (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                     O2)))))
                                 (a!94 (@0anypath (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                              O2)))))
                                 (a!96 (Build_CookieMapping
                                         (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                     O2)))
                                         (sc_value (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                      O2)))))
                                 (a!98 (not (sc_secure (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                          O2)))))
                                 (a!100 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            O2)))
                                           SSLax))
                                 (a!101 (= (sc_same_site (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            O2)))
                                           SSNone))
                                 (a!103 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                            O2)))))
                                 (a!104 (@0domain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!105 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                       O2)))))
                                 (a!107 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        O2)))))
                                 (a!108 (@0SomeDomain (sc_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!112 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                             O2)))
                                           (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!114 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      O2)))))
                                 (a!115 (@0anypath (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                               O2)))))
                                 (a!117 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                      O2)))
                                          (sc_value (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                       O2)))))
                                 (a!119 (not (sc_secure (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                           O2)))))
                                 (a!121 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            O2)))
                                           SSLax))
                                 (a!122 (= (sc_same_site (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            O2)))
                                           SSNone))
                                 (a!124 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                            O2)))))
                                 (a!125 (@0domain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!126 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                       O2)))))
                                 (a!128 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        O2)))))
                                 (a!129 (@0SomeDomain (sc_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!133 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                             O2)))
                                           (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!135 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      O2)))))
                                 (a!136 (@0anypath (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                               O2)))))
                                 (a!138 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                      O2)))
                                          (sc_value (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                       O2)))))
                                 (a!140 (not (sc_secure (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                           O2)))))
                                 (a!142 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            O2)))
                                           SSLax))
                                 (a!143 (= (sc_same_site (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            O2)))
                                           SSNone))
                                 (a!145 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                            O2)))))
                                 (a!146 (@0domain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!147 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                       O2)))))
                                 (a!149 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        O2)))))
                                 (a!150 (@0SomeDomain (sc_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!154 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                             O2)))
                                           (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!156 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      O2)))))
                                 (a!157 (@0anypath (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                               O2)))))
                                 (a!159 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                      O2)))
                                          (sc_value (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                       O2)))))
                                 (a!161 (not (sc_secure (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                           O2)))))
                                 (a!163 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            O2)))
                                           SSLax))
                                 (a!164 (= (sc_same_site (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            O2)))
                                           SSNone))
                                 (a!166 ((_ is domain)
                                          (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                            O2)))))
                                 (a!167 (@0domain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!168 (@1subdomain (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                       O2)))))
                                 (a!170 ((_ is SomeDomain)
                                          (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        O2)))))
                                 (a!171 (@0SomeDomain (sc_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                    O2)))))
                                 (a!175 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                             O2)))
                                           (@0SomeDomain (url_host (rq_url K2)))))
                                 (a!177 ((_ is slash)
                                          (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      O2)))))
                                 (a!178 (@0anypath (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                               O2)))))
                                 (a!180 (Build_CookieMapping
                                          (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                      O2)))
                                          (sc_value (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                       O2)))))
                                 (a!185 (= (rq_hd_cookie (rq_headers K2))
                                           (Build_ArrayoptionCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping
                                             NoneCookieMapping)))
                                 (a!187 (ite (= G2 2)
                                             (@2ArrayoptionBlob P2)
                                             (ite (= G2 3)
                                                  (@3ArrayoptionBlob P2)
                                                  (ite (= G2 4)
                                                       (@4ArrayoptionBlob P2)
                                                       (@defaultArrayoptionBlob
                                                         P2)))))
                                 (a!190 (= (@0DOMIndex (@1DOMPath (@0EmitterScript T1)))
                                           0))
                                 (a!191 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!192 (= (@0DOMIndex (@1DOMPath (@0EmitterScript T1)))
                                           1))
                                 (a!193 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!194 (= (@0DOMIndex (@1DOMPath (@0EmitterScript T1)))
                                           2))
                                 (a!195 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!196 (= (@0DOMIndex (@1DOMPath (@0EmitterScript T1)))
                                           3))
                                 (a!197 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!198 (= (@0DOMIndex (@1DOMPath (@0EmitterScript T1)))
                                           4))
                                 (a!199 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!200 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document V1)))))
                                 (a!207 (not ((_ is DOMTopLevel)
                                               (@1DOMPath (@0EmitterScript T1)))))
                                 (a!208 (and (c_earlyhtml5_form_methods
                                               (config S1))
                                             ((_ is MethodDelete)
                                               (form_method (@1EmitterForm T1)))))
                                 (a!211 (= (@0DOMIndex (@1DOMPath (@0EmitterForm T1)))
                                           0))
                                 (a!212 (= (@0DOMIndex (@1DOMPath (@0EmitterForm T1)))
                                           1))
                                 (a!213 (= (@0DOMIndex (@1DOMPath (@0EmitterForm T1)))
                                           2))
                                 (a!214 (= (@0DOMIndex (@1DOMPath (@0EmitterForm T1)))
                                           3))
                                 (a!215 (= (@0DOMIndex (@1DOMPath (@0EmitterForm T1)))
                                           4))
                                 (a!218 (not ((_ is DOMTopLevel)
                                               (@1DOMPath (@0EmitterForm T1)))))
                                 (a!220 ((_ is ProtocolHTTPS)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  T1)))))
                                 (a!221 ((_ is ProtocolHTTP)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  T1)))))
                                 (a!222 (TupleOrigin (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                             T1)))
                                                     (url_host (rq_url (@1EmitterCORSPreflight
                                                                         T1)))
                                                     (url_port (rq_url (@1EmitterCORSPreflight
                                                                         T1)))))
                                 (a!223 ((_ is ProtocolData)
                                          (url_protocol (rq_url (@1EmitterCORSPreflight
                                                                  T1)))))
                                 (a!224 ((_ is url_path_data)
                                          (url_path (rq_url (@1EmitterCORSPreflight
                                                              T1)))))
                                 (a!225 (@0url_path_data (url_path (rq_url (@1EmitterCORSPreflight
                                                                             T1)))))
                                 (a!226 ((_ is url_path_blob)
                                          (url_path (rq_url (@1EmitterCORSPreflight
                                                              T1)))))
                                 (a!227 (@0url_path_blob (url_path (rq_url (@1EmitterCORSPreflight
                                                                             T1)))))
                                 (a!230 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location V1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location V1)))))
                                 (a!231 (SomeOrigin (TupleOrigin (url_protocol (wd_location V1))
                                                                 (url_host (wd_location V1))
                                                                 (url_port (wd_location V1)))))
                                 (a!232 (OpaqueOrigin (@0url_path_data (url_path (wd_location V1)))))
                                 (a!234 (SomeOrigin (@0url_path_blob (url_path (wd_location V1)))))
                                 (a!239 (not (= (rq_method (@1EmitterCORSPreflight
                                                             T1))
                                                MethodGet)))
                                 (a!240 (not (= (rq_method (@1EmitterCORSPreflight
                                                             T1))
                                                MethodPost)))
                                 (a!242 (and (= (rq_hd_origin (rq_headers K2))
                                                NoneOrigin)
                                             (= (rq_method K2) MethodGet)
                                             (= (rq_hd_referer (rq_headers K2))
                                                NoneURL)))
                                 (a!243 (SomeOrigin (TupleOrigin (url_protocol (rq_url K2))
                                                                 (url_host (rq_url K2))
                                                                 (url_port (rq_url K2)))))
                                 (a!244 (OpaqueOrigin (@0url_path_data (url_path (rq_url K2)))))
                                 (a!246 (SomeOrigin (@0url_path_blob (url_path (rq_url K2)))))
                                 (a!250 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter J2))
                                                4)
                                             (@4ArrayEmitter (emitters S1))
                                             (@defaultArrayEmitter
                                               (emitters S1))))
                                 (a!255 (rp_hd_access_control_allow_origin
                                          (rp_headers (@0SomeResponse (ft_response J2)))))
                                 (a!261 ((_ is SomeReferrerPolicy)
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document V1)))))
                                 (a!262 (@0SomeReferrerPolicy
                                          (rp_hd_referrer_policy
                                            (dc_headers (wd_document V1)))))
                                 (a!268 (not ((_ is MethodDelete)
                                               (form_method (@1EmitterForm T1)))))
                                 (a!275 (and (or (= T1 EmitterClient)
                                                 (= T1 EmitterWorker)
                                                 (= T1 (EmitterForm C2 D2))
                                                 (= T1 (EmitterScript A2 B2)))
                                             (not (c_redirect_preflight_requests
                                                    (config S1)))))
                                 (a!277 (= (rq_hd_origin (rq_headers K2))
                                           (rq_hd_origin (rq_headers (ft_request J2)))))
                                 (a!278 ((_ is ProtocolHTTPS)
                                          (url_protocol (rq_url (ft_request J2)))))
                                 (a!279 ((_ is ProtocolHTTP)
                                          (url_protocol (rq_url (ft_request J2)))))
                                 (a!280 (TupleOrigin (url_protocol (rq_url (ft_request J2)))
                                                     (url_host (rq_url (ft_request J2)))
                                                     (url_port (rq_url (ft_request J2)))))
                                 (a!281 ((_ is ProtocolData)
                                          (url_protocol (rq_url (ft_request J2)))))
                                 (a!282 ((_ is url_path_data)
                                          (url_path (rq_url (ft_request J2)))))
                                 (a!283 (@0url_path_data (url_path (rq_url (ft_request J2)))))
                                 (a!284 ((_ is url_path_blob)
                                          (url_path (rq_url (ft_request J2)))))
                                 (a!285 (@0url_path_blob (url_path (rq_url (ft_request J2)))))
                                 (a!297 (consEvent (EvRequest T1
                                                              K2
                                                              (+ 1
                                                                 (ft_correlator J2)))
                                                   L2)))
                           (let ((a!5 (and a!3
                                           a!4
                                           ((_ is SomeInt)
                                             (url_port (rq_url K2)))
                                           ((_ is SomeDomain)
                                             (url_host (rq_url K2)))))
                                 (a!8 (and ((_ is url_path_data)
                                             (url_path (rq_url K2)))
                                           a!6
                                           a!7))
                                 (a!9 (and ((_ is url_path_blob)
                                             (url_path (rq_url K2)))
                                           a!4
                                           a!6
                                           a!7))
                                 (a!17 (ite (= Z 2)
                                            a!13
                                            (ite (= Z 3)
                                                 a!14
                                                 (ite (= Z 4) a!15 a!16))))
                                 (a!26 (ite (= L 2)
                                            a!22
                                            (ite (= L 3)
                                                 a!23
                                                 (ite (= L 4) a!24 a!25))))
                                 (a!38 (ite (= P1 2)
                                            a!34
                                            (ite (= P1 3)
                                                 a!35
                                                 (ite (= P1 4) a!36 a!37))))
                                 (a!44 (ite (= D1 1)
                                            (@1ArrayEmitter (emitters S1))
                                            (ite (= D1 2)
                                                 (@2ArrayEmitter (emitters S1))
                                                 a!43)))
                                 (a!48 (or a!47
                                           (= (url_protocol (rq_url K2))
                                              ProtocolHTTPS)))
                                 (a!51 (ite ((_ is EmitterClient) T1)
                                            (or a!49 a!50)
                                            (ite (or ((_ is EmitterForm) T1)
                                                     ((_ is EmitterScript) T1))
                                                 a!50
                                                 (and ((_ is EmitterWorker) T1)
                                                      a!50))))
                                 (a!65 (ite ((_ is domain) a!62)
                                            (= a!63 (@0domain a!62))
                                            (and (= a!64 (@0subdomain a!62))
                                                 (= a!63 (@1subdomain a!62)))))
                                 (a!69 (and ((_ is SomeDomain)
                                              (url_host (rq_url K2)))
                                            a!68))
                                 (a!78 (or a!77
                                           (= (url_protocol (rq_url K2))
                                              ProtocolHTTPS)))
                                 (a!81 (ite ((_ is EmitterClient) T1)
                                            (or a!79 a!80)
                                            (ite (or ((_ is EmitterForm) T1)
                                                     ((_ is EmitterScript) T1))
                                                 a!80
                                                 (and ((_ is EmitterWorker) T1)
                                                      a!80))))
                                 (a!88 (ite ((_ is domain) a!87)
                                            (= a!63 (@0domain a!87))
                                            (and (= a!64 (@0subdomain a!87))
                                                 (= a!63 (@1subdomain a!87)))))
                                 (a!92 (and ((_ is SomeDomain)
                                              (url_host (rq_url K2)))
                                            a!91))
                                 (a!99 (or a!98
                                           (= (url_protocol (rq_url K2))
                                              ProtocolHTTPS)))
                                 (a!102 (ite ((_ is EmitterClient) T1)
                                             (or a!100 a!101)
                                             (ite (or ((_ is EmitterForm) T1)
                                                      ((_ is EmitterScript) T1))
                                                  a!101
                                                  (and ((_ is EmitterWorker) T1)
                                                       a!101))))
                                 (a!109 (ite ((_ is domain) a!108)
                                             (= a!63 (@0domain a!108))
                                             (and (= a!64 (@0subdomain a!108))
                                                  (= a!63 (@1subdomain a!108)))))
                                 (a!113 (and ((_ is SomeDomain)
                                               (url_host (rq_url K2)))
                                             a!112))
                                 (a!120 (or a!119
                                            (= (url_protocol (rq_url K2))
                                               ProtocolHTTPS)))
                                 (a!123 (ite ((_ is EmitterClient) T1)
                                             (or a!121 a!122)
                                             (ite (or ((_ is EmitterForm) T1)
                                                      ((_ is EmitterScript) T1))
                                                  a!122
                                                  (and ((_ is EmitterWorker) T1)
                                                       a!122))))
                                 (a!130 (ite ((_ is domain) a!129)
                                             (= a!63 (@0domain a!129))
                                             (and (= a!64 (@0subdomain a!129))
                                                  (= a!63 (@1subdomain a!129)))))
                                 (a!134 (and ((_ is SomeDomain)
                                               (url_host (rq_url K2)))
                                             a!133))
                                 (a!141 (or a!140
                                            (= (url_protocol (rq_url K2))
                                               ProtocolHTTPS)))
                                 (a!144 (ite ((_ is EmitterClient) T1)
                                             (or a!142 a!143)
                                             (ite (or ((_ is EmitterForm) T1)
                                                      ((_ is EmitterScript) T1))
                                                  a!143
                                                  (and ((_ is EmitterWorker) T1)
                                                       a!143))))
                                 (a!151 (ite ((_ is domain) a!150)
                                             (= a!63 (@0domain a!150))
                                             (and (= a!64 (@0subdomain a!150))
                                                  (= a!63 (@1subdomain a!150)))))
                                 (a!155 (and ((_ is SomeDomain)
                                               (url_host (rq_url K2)))
                                             a!154))
                                 (a!162 (or a!161
                                            (= (url_protocol (rq_url K2))
                                               ProtocolHTTPS)))
                                 (a!165 (ite ((_ is EmitterClient) T1)
                                             (or a!163 a!164)
                                             (ite (or ((_ is EmitterForm) T1)
                                                      ((_ is EmitterScript) T1))
                                                  a!164
                                                  (and ((_ is EmitterWorker) T1)
                                                       a!164))))
                                 (a!172 (ite ((_ is domain) a!171)
                                             (= a!63 (@0domain a!171))
                                             (and (= a!64 (@0subdomain a!171))
                                                  (= a!63 (@1subdomain a!171)))))
                                 (a!176 (and ((_ is SomeDomain)
                                               (url_host (rq_url K2)))
                                             a!175))
                                 (a!186 (and (= T1 EmitterClient)
                                             (= (url_protocol (rq_url K2))
                                                ProtocolData)
                                             a!185))
                                 (a!188 (= (ite (= G2 0)
                                                (@0ArrayoptionBlob P2)
                                                (ite (= G2 1)
                                                     (@1ArrayoptionBlob P2)
                                                     a!187))
                                           (SomeBlob H2)))
                                 (a!201 (ite a!192
                                             a!193
                                             (ite a!194
                                                  a!195
                                                  (ite a!196
                                                       a!197
                                                       (ite a!198 a!199 a!200)))))
                                 (a!209 (ite ((_ is MethodPut)
                                               (form_method (@1EmitterForm T1)))
                                             (c_earlyhtml5_form_methods
                                               (config S1))
                                             a!208))
                                 (a!216 (ite a!212
                                             a!193
                                             (ite a!213
                                                  a!195
                                                  (ite a!214
                                                       a!197
                                                       (ite a!215 a!199 a!200)))))
                                 (a!228 (ite a!223
                                             (ite a!224
                                                  (SomeOrigin (OpaqueOrigin a!225))
                                                  NoneOrigin)
                                             (ite a!224
                                                  NoneOrigin
                                                  (ite a!226
                                                       (SomeOrigin a!227)
                                                       NoneOrigin))))
                                 (a!233 (ite ((_ is url_path_data)
                                               (url_path (wd_location V1)))
                                             (SomeOrigin a!232)
                                             NoneOrigin))
                                 (a!235 (ite ((_ is url_path_blob)
                                               (url_path (wd_location V1)))
                                             a!234
                                             NoneOrigin))
                                 (a!245 (ite ((_ is url_path_data)
                                               (url_path (rq_url K2)))
                                             (SomeOrigin a!244)
                                             NoneOrigin))
                                 (a!247 (ite ((_ is url_path_blob)
                                               (url_path (rq_url K2)))
                                             a!246
                                             NoneOrigin))
                                 (a!251 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter J2))
                                                3)
                                             (@3ArrayEmitter (emitters S1))
                                             a!250))
                                 (a!256 (= (@0SomeOrigin a!255)
                                           (@0SomeOrigin (rq_hd_origin (rq_headers K2)))))
                                 (a!286 (ite a!281
                                             (ite a!282
                                                  (SomeOrigin (OpaqueOrigin a!283))
                                                  NoneOrigin)
                                             (ite a!282
                                                  NoneOrigin
                                                  (ite a!284
                                                       (SomeOrigin a!285)
                                                       NoneOrigin)))))
                           (let ((a!10 (ite ((_ is ProtocolData)
                                              (url_protocol (rq_url K2)))
                                            a!8
                                            a!9))
                                 (a!18 (ite (= Z 0)
                                            a!11
                                            (ite (= Z 1) a!12 a!17)))
                                 (a!27 (ite (= L 0)
                                            a!20
                                            (ite (= L 1) a!21 a!26)))
                                 (a!39 (ite (= P1 0)
                                            a!32
                                            (ite (= P1 1) a!33 a!38)))
                                 (a!45 (= (ite (= D1 0)
                                               (@0ArrayEmitter (emitters S1))
                                               a!44)
                                          (EmitterScript F1 E1)))
                                 (a!58 (or a!51
                                           (ite a!52
                                                (ite a!53
                                                     (= a!54 a!55)
                                                     (= a!54 a!56))
                                                (ite a!53
                                                     (= a!57 a!55)
                                                     (= a!57 a!56)))))
                                 (a!66 (ite a!60
                                            (and (= a!61 (@0domain a!62))
                                                 ((_ is domain) a!62))
                                            a!65))
                                 (a!85 (or a!81
                                           (ite a!52
                                                (ite a!82
                                                     (= a!54 a!83)
                                                     (= a!54 a!84))
                                                (ite a!82
                                                     (= a!57 a!83)
                                                     (= a!57 a!84)))))
                                 (a!89 (ite a!60
                                            (and (= a!61 (@0domain a!87))
                                                 ((_ is domain) a!87))
                                            a!88))
                                 (a!106 (or a!102
                                            (ite a!52
                                                 (ite a!103
                                                      (= a!54 a!104)
                                                      (= a!54 a!105))
                                                 (ite a!103
                                                      (= a!57 a!104)
                                                      (= a!57 a!105)))))
                                 (a!110 (ite a!60
                                             (and (= a!61 (@0domain a!108))
                                                  ((_ is domain) a!108))
                                             a!109))
                                 (a!127 (or a!123
                                            (ite a!52
                                                 (ite a!124
                                                      (= a!54 a!125)
                                                      (= a!54 a!126))
                                                 (ite a!124
                                                      (= a!57 a!125)
                                                      (= a!57 a!126)))))
                                 (a!131 (ite a!60
                                             (and (= a!61 (@0domain a!129))
                                                  ((_ is domain) a!129))
                                             a!130))
                                 (a!148 (or a!144
                                            (ite a!52
                                                 (ite a!145
                                                      (= a!54 a!146)
                                                      (= a!54 a!147))
                                                 (ite a!145
                                                      (= a!57 a!146)
                                                      (= a!57 a!147)))))
                                 (a!152 (ite a!60
                                             (and (= a!61 (@0domain a!150))
                                                  ((_ is domain) a!150))
                                             a!151))
                                 (a!169 (or a!165
                                            (ite a!52
                                                 (ite a!166
                                                      (= a!54 a!167)
                                                      (= a!54 a!168))
                                                 (ite a!166
                                                      (= a!57 a!167)
                                                      (= a!57 a!168)))))
                                 (a!173 (ite a!60
                                             (and (= a!61 (@0domain a!171))
                                                  ((_ is domain) a!171))
                                             a!172))
                                 (a!189 (and (= T1 EmitterClient)
                                             (= (blob_origin H2) I2)
                                             (= (rq_url K2) (blob_url H2))
                                             (= (url_protocol (rq_url K2))
                                                ProtocolBlob)
                                             a!185
                                             (= (url_path (rq_url K2))
                                                (url_path_blob I2 G2))
                                             a!188))
                                 (a!202 (@0ContentElementScript
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!190
                                                                   a!191
                                                                   a!201)))))
                                 (a!203 ((_ is ContentElementScript)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!190
                                                                   a!191
                                                                   a!201)))))
                                 (a!204 ((_ is ContentElementImage)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!190
                                                                   a!191
                                                                   a!201)))))
                                 (a!205 ((_ is ContentElementHTML)
                                          (@1DOMElementResource
                                            (@0SomeDOMElement (ite a!190
                                                                   a!191
                                                                   a!201)))))
                                 (a!206 (not ((_ is DOMElementForm)
                                               (@0SomeDOMElement (ite a!190
                                                                      a!191
                                                                      a!201)))))
                                 (a!210 (or ((_ is MethodPost)
                                              (form_method (@1EmitterForm T1)))
                                            ((_ is MethodGet)
                                              (form_method (@1EmitterForm T1)))
                                            a!209))
                                 (a!217 (= (@0DOMElementForm (@0SomeDOMElement (ite a!211
                                                                                    a!191
                                                                                    a!216)))
                                           (@1EmitterForm T1)))
                                 (a!229 (not (= (ite (or a!220 a!221)
                                                     (SomeOrigin a!222)
                                                     a!228)
                                                NoneOrigin)))
                                 (a!236 (ite ((_ is url_path_data)
                                               (url_path (wd_location V1)))
                                             NoneOrigin
                                             a!235))
                                 (a!248 (ite ((_ is url_path_data)
                                               (url_path (rq_url K2)))
                                             NoneOrigin
                                             a!247))
                                 (a!252 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter J2))
                                                2)
                                             (@2ArrayEmitter (emitters S1))
                                             a!251)))
                           (let ((a!19 (and ((_ is DOMElementForm)
                                              (@0SomeDOMElement a!18))
                                            ((_ is SomeDOMElement) a!18)
                                            (= O B1)
                                            (= (@0DOMElementForm (@0SomeDOMElement a!18))
                                               B1)
                                            (= T1 (EmitterForm P O))
                                            (= V1 A1)
                                            (= U1 Q)
                                            (= A1 V)
                                            (= V W)
                                            (= Q W)
                                            (= P X)
                                            (= X T)
                                            (= X (DOMPath Y (DOMIndex Z)))
                                            (= T (DOMPath nilInt U))
                                            (= R S)
                                            (= S1 R)))
                                 (a!28 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!27)))
                                          N))
                                 (a!29 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!27)))))
                                 (a!30 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!27)))))
                                 (a!40 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!39)))
                                          R1))
                                 (a!41 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!39)))))
                                 (a!42 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!39)))))
                                 (a!67 (and a!66
                                            ((_ is SomeDomain)
                                              (url_host (rq_url K2)))))
                                 (a!90 (and a!89
                                            ((_ is SomeDomain)
                                              (url_host (rq_url K2)))))
                                 (a!111 (and a!110
                                             ((_ is SomeDomain)
                                               (url_host (rq_url K2)))))
                                 (a!132 (and a!131
                                             ((_ is SomeDomain)
                                               (url_host (rq_url K2)))))
                                 (a!153 (and a!152
                                             ((_ is SomeDomain)
                                               (url_host (rq_url K2)))))
                                 (a!174 (and a!173
                                             ((_ is SomeDomain)
                                               (url_host (rq_url K2)))))
                                 (a!219 (and a!210
                                             ((_ is DOMElementForm)
                                               (@0SomeDOMElement (ite a!211
                                                                      a!191
                                                                      a!216)))
                                             ((_ is SomeDOMElement)
                                               (ite a!211 a!191 a!216))
                                             a!217
                                             a!218))
                                 (a!237 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location V1)))
                                             a!233
                                             a!236))
                                 (a!249 (ite ((_ is ProtocolData)
                                               (url_protocol (rq_url K2)))
                                             a!245
                                             a!248))
                                 (a!253 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter J2))
                                                1)
                                             (@1ArrayEmitter (emitters S1))
                                             a!252)))
                           (let ((a!31 (and (= A N)
                                            a!28
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!27)))
                                            a!29
                                            a!30
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!27)))
                                            ((_ is SomeDOMElement) a!27)
                                            (= T1 (EmitterScript B A))
                                            (= V1 M)
                                            (= U1 C)
                                            (= M H)
                                            (= H I)
                                            (= C I)
                                            (= F (DOMPath nilInt G))
                                            (= B J)
                                            (= J F)
                                            (= J (DOMPath K (DOMIndex L)))
                                            (= S1 D)
                                            (= D E)))
                                 (a!46 (and (= E1 R1)
                                            a!40
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!39)))
                                            a!41
                                            a!42
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!39)))
                                            ((_ is SomeDOMElement) a!39)
                                            (= T1 (EmitterCORSPreflight D1 C1))
                                            a!45
                                            (= V1 Q1)
                                            (= Q1 L1)
                                            (= L1 M1)
                                            (= U1 G1)
                                            (= G1 M1)
                                            (= F1 N1)
                                            (= N1 J1)
                                            (= N1 (DOMPath O1 (DOMIndex P1)))
                                            (= J1 (DOMPath nilInt K1))
                                            (= S1 H1)
                                            (= H1 I1)))
                                 (a!74 (and a!48
                                            a!58
                                            (ite a!59 a!67 a!69)
                                            (ite a!70
                                                 a!71
                                                 (or a!71 (= a!72 a!73)))
                                            a!3
                                            a!4))
                                 (a!95 (and a!78
                                            a!85
                                            (ite a!86 a!90 a!92)
                                            (ite a!70
                                                 a!93
                                                 (or a!93 (= a!72 a!94)))
                                            a!3
                                            a!4))
                                 (a!116 (and a!99
                                             a!106
                                             (ite a!107 a!111 a!113)
                                             (ite a!70
                                                  a!114
                                                  (or a!114 (= a!72 a!115)))
                                             a!3
                                             a!4))
                                 (a!137 (and a!120
                                             a!127
                                             (ite a!128 a!132 a!134)
                                             (ite a!70
                                                  a!135
                                                  (or a!135 (= a!72 a!136)))
                                             a!3
                                             a!4))
                                 (a!158 (and a!141
                                             a!148
                                             (ite a!149 a!153 a!155)
                                             (ite a!70
                                                  a!156
                                                  (or a!156 (= a!72 a!157)))
                                             a!3
                                             a!4))
                                 (a!179 (and a!162
                                             a!169
                                             (ite a!170 a!174 a!176)
                                             (ite a!70
                                                  a!177
                                                  (or a!177 (= a!72 a!178)))
                                             a!3
                                             a!4))
                                 (a!238 (not (= (ite (or a!220 a!221)
                                                     (SomeOrigin a!222)
                                                     a!228)
                                                (ite a!230 a!231 a!237))))
                                 (a!254 (ite (= (@0EmitterCORSPreflight
                                                  (ft_emitter J2))
                                                0)
                                             (@0ArrayEmitter (emitters S1))
                                             a!253))
                                 (a!259 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!230
                                                                  a!231
                                                                  a!237)))
                                             (ite a!230 a!231 a!237)
                                             NoneOrigin))
                                 (a!263 (Build_URL (@0TupleOrigin (@0SomeOrigin (ite a!230
                                                                                     a!231
                                                                                     a!237)))
                                                   (@1TupleOrigin (@0SomeOrigin (ite a!230
                                                                                     a!231
                                                                                     a!237)))
                                                   (@2TupleOrigin (@0SomeOrigin (ite a!230
                                                                                     a!231
                                                                                     a!237)))
                                                   (url_path_res slash)))
                                 (a!267 (and (c_earlyhtml5_form_methods
                                               (config S1))
                                             (not (= (ite a!2 a!243 a!249)
                                                     NoneOrigin))
                                             (= (ite a!2 a!243 a!249)
                                                (ite a!230 a!231 a!237))))
                                 (a!287 (= (ite a!2 a!243 a!249)
                                           (ite (or a!278 a!279)
                                                (SomeOrigin a!280)
                                                a!286))))
                           (let ((a!76 (ite ((_ is SomeDomain)
                                              (url_host (wd_location V1)))
                                            (ite a!74
                                                 (SomeCookieMapping a!75)
                                                 NoneCookieMapping)
                                            NoneCookieMapping))
                                 (a!97 (ite ((_ is SomeDomain)
                                              (url_host (wd_location V1)))
                                            (ite a!95
                                                 (SomeCookieMapping a!96)
                                                 NoneCookieMapping)
                                            NoneCookieMapping))
                                 (a!118 (ite ((_ is SomeDomain)
                                               (url_host (wd_location V1)))
                                             (ite a!116
                                                  (SomeCookieMapping a!117)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!139 (ite ((_ is SomeDomain)
                                               (url_host (wd_location V1)))
                                             (ite a!137
                                                  (SomeCookieMapping a!138)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!160 (ite ((_ is SomeDomain)
                                               (url_host (wd_location V1)))
                                             (ite a!158
                                                  (SomeCookieMapping a!159)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!181 (ite ((_ is SomeDomain)
                                               (url_host (wd_location V1)))
                                             (ite a!179
                                                  (SomeCookieMapping a!180)
                                                  NoneCookieMapping)
                                             NoneCookieMapping))
                                 (a!241 (ite ((_ is EmitterScript) T1)
                                             (and (= a!202 (@1EmitterScript T1))
                                                  a!203
                                                  (not a!204)
                                                  (not a!205)
                                                  a!206
                                                  ((_ is SomeDOMElement)
                                                    (ite a!190 a!191 a!201))
                                                  a!207)
                                             (ite ((_ is EmitterForm) T1)
                                                  a!219
                                                  (or ((_ is EmitterWorker) T1)
                                                      (and a!229
                                                           a!238
                                                           a!239
                                                           a!240)))))
                                 (a!257 (and (= T1 a!254)
                                             (not ((_ is EmitterWorker)
                                                    (ft_emitter J2)))
                                             (not ((_ is EmitterForm)
                                                    (ft_emitter J2)))
                                             (not ((_ is EmitterScript)
                                                    (ft_emitter J2)))
                                             (not ((_ is EmitterClient)
                                                    (ft_emitter J2)))
                                             ((_ is SomeOrigin) a!255)
                                             ((_ is SomeOrigin)
                                               (rq_hd_origin (rq_headers K2)))
                                             (= K2
                                                (@1EmitterCORSPreflight
                                                  (ft_emitter J2)))
                                             a!256
                                             ((_ is SomeResponse)
                                               (ft_response J2))))
                                 (a!260 (= (rq_hd_origin (rq_headers K2))
                                           (ite ((_ is SomeOrigin)
                                                  (ite a!230 a!231 a!237))
                                                a!259
                                                (ite a!230 a!231 a!237))))
                                 (a!264 (ite ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!230
                                                                  a!231
                                                                  a!237)))
                                             (SomeURL a!263)
                                             NoneURL))
                                 (a!269 (ite ((_ is MethodPut)
                                               (form_method (@1EmitterForm T1)))
                                             a!267
                                             (or a!267 a!268)))
                                 (a!288 (and (= (rq_hd_origin (rq_headers K2))
                                                NoneOrigin)
                                             (not a!287))))
                           (let ((a!182 (Build_ArrayoptionCookieMapping
                                          (ite ((_ is SomeSetCookie)
                                                 (@0ArrayoptionSetCookie O2))
                                               a!76
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@1ArrayoptionSetCookie O2))
                                               a!97
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@2ArrayoptionSetCookie O2))
                                               a!118
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@3ArrayoptionSetCookie O2))
                                               a!139
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@4ArrayoptionSetCookie O2))
                                               a!160
                                               NoneCookieMapping)
                                          (ite ((_ is SomeSetCookie)
                                                 (@defaultArrayoptionSetCookie
                                                   O2))
                                               a!181
                                               NoneCookieMapping)))
                                 (a!258 (or (= (rq_method K2) MethodGet)
                                            (= (rq_method K2) MethodPost)
                                            (= (ite a!2 a!243 a!249)
                                               (ite a!230 a!231 a!237))
                                            (= (ite a!2 a!243 a!249) NoneOrigin)
                                            a!257))
                                 (a!265 (ite ((_ is ReferrerPolicyNoReferrer)
                                               a!262)
                                             NoneURL
                                             (ite ((_ is SomeOrigin)
                                                    (ite a!230 a!231 a!237))
                                                  a!264
                                                  NoneURL)))
                                 (a!270 (or ((_ is MethodPost)
                                              (form_method (@1EmitterForm T1)))
                                            ((_ is MethodGet)
                                              (form_method (@1EmitterForm T1)))
                                            a!269))
                                 (a!289 (and (or (and a!277 a!287) a!288)
                                             (not (c_origin_header_on_cross_origin_redirect
                                                    (config S1))))))
                           (let ((a!183 (and (= (url_protocol (rq_url K2))
                                                ProtocolHTTP)
                                             (= (rq_hd_cookie (rq_headers K2))
                                                a!182)))
                                 (a!184 (and (= (url_protocol (rq_url K2))
                                                ProtocolHTTPS)
                                             (= (rq_hd_cookie (rq_headers K2))
                                                a!182)))
                                 (a!266 (and a!258
                                             a!260
                                             (= (rq_hd_referer (rq_headers K2))
                                                (ite a!261 a!265 NoneURL))))
                                 (a!271 (and a!270
                                             a!260
                                             (= (rq_method K2)
                                                (form_method (@1EmitterForm T1)))
                                             (= (rq_hd_referer (rq_headers K2))
                                                (ite a!261 a!265 NoneURL))
                                             (= (rq_url K2)
                                                (form_action (@1EmitterForm T1)))))
                                 (a!272 (and a!258
                                             a!260
                                             (= (rq_hd_referer (rq_headers K2))
                                                NoneURL)))
                                 (a!273 (and a!260
                                             (not (= (ite a!2 a!243 a!249)
                                                     NoneOrigin))
                                             (not (= (ite a!2 a!243 a!249)
                                                     (ite a!230 a!231 a!237)))
                                             (= (rq_method K2) MethodOptions)
                                             (= (rq_hd_referer (rq_headers K2))
                                                (ite a!261 a!265 NoneURL))
                                             (= (rq_url K2)
                                                (rq_url (@1EmitterCORSPreflight
                                                          T1)))))
                                 (a!290 (or (and (c_origin_header_on_cross_origin_redirect
                                                   (config S1))
                                                 a!277)
                                            a!289)))
                           (let ((a!274 (ite ((_ is EmitterScript) T1)
                                             a!266
                                             (ite ((_ is EmitterForm) T1)
                                                  a!271
                                                  (ite ((_ is EmitterWorker) T1)
                                                       a!272
                                                       a!273))))
                                 (a!291 (and a!290
                                             (= (ft_emitter J2) T1)
                                             (= (rq_method K2) MethodGet)
                                             (= (rp_hd_location (rp_headers F2))
                                                (SomeURL Z1))
                                             (= (rq_hd_referer (rq_headers K2))
                                                NoneURL)
                                             (= (rq_url K2) Z1)
                                             (= (rq_body K2) NoneInt)))
                                 (a!293 (and a!290
                                             (= (ft_emitter J2) T1)
                                             (= (rq_method K2)
                                                (rq_method (ft_request J2)))
                                             (= (rp_hd_location (rp_headers F2))
                                                (SomeURL E2))
                                             (= (rq_hd_referer (rq_headers K2))
                                                NoneURL)
                                             (= (rq_url K2) E2)
                                             (= (rq_body K2)
                                                (rq_body (ft_request J2))))))
                           (let ((a!276 (and (ite ((_ is EmitterClient) T1)
                                                  a!242
                                                  a!274)
                                             (= (rp_hd_location (rp_headers F2))
                                                NoneURL))))
                           (let ((a!292 (and (or (c_redirect_preflight_requests
                                                   (config S1))
                                                 a!275)
                                             (or a!276 a!291)
                                             (= (rp_code F2) ResponseFound)))
                                 (a!294 (and (or (c_redirect_preflight_requests
                                                   (config S1))
                                                 a!275)
                                             (or a!276 a!293)
                                             (= (rp_code F2)
                                                ResponseTemporaryRedirect))))
                           (let ((a!295 (or (and (ite ((_ is EmitterClient) T1)
                                                      a!242
                                                      a!274)
                                                 (= (rp_code F2) ResponseOk))
                                            (and (ite ((_ is EmitterClient) T1)
                                                      a!242
                                                      a!274)
                                                 (= (rp_code F2)
                                                    ResponseNoContent))
                                            a!292
                                            a!294)))
                           (let ((a!296 (or (and a!295
                                                 (= (ft_response J2)
                                                    (SomeResponse F2)))
                                            (and (ite ((_ is EmitterClient) T1)
                                                      a!242
                                                      a!274)
                                                 (= (ft_response J2)
                                                    NoneResponse)))))
                           (let ((a!298 (and (Reachable S1 L2 W1)
                                             (= X1 a!1)
                                             (= W1
                                                (Build_State M2
                                                             J2
                                                             N2
                                                             U1
                                                             O2
                                                             P2
                                                             Q2))
                                             (ite a!2 a!5 a!10)
                                             (or (and (= T1 EmitterClient)
                                                      (= V1 U1))
                                                 (and (= T1 EmitterWorker)
                                                      (= V1 U1))
                                                 a!19
                                                 a!31
                                                 a!46)
                                             (or a!183 a!184 a!186 a!189)
                                             (or ((_ is EmitterClient) T1)
                                                 a!241)
                                             a!296
                                             (= Y1 a!297))))
                             (=> a!298 (Reachable S1 Y1 X1))))))))))))))))
                           :weight 0))))
      (a!96 (asserted (forall ((A State)
                               (B State)
                               (C listEvent)
                               (D Int)
                               (E Response)
                               (F NestedDOMPath)
                               (G DOMSelector)
                               (H Window)
                               (I listInt)
                               (J Int)
                               (K Script)
                               (L Global)
                               (M DOMSelector)
                               (N ServiceWorker)
                               (O Int)
                               (P optionInt)
                               (Q listEvent)
                               (R Int)
                               (S FetchEngine)
                               (T ServiceWorker)
                               (U ArrayoptionSetCookie)
                               (V ArrayoptionBlob)
                               (W ArrayoptionStorageItem))
                        (! (let ((a!1 (ite (= O 4)
                                           (Build_ArrayoptionInt
                                             (@0ArrayoptionInt (wk_cache N))
                                             (@1ArrayoptionInt (wk_cache N))
                                             (@2ArrayoptionInt (wk_cache N))
                                             (@3ArrayoptionInt (wk_cache N))
                                             P
                                             (@defaultArrayoptionInt
                                               (wk_cache N)))
                                           (wk_cache N)))
                                 (a!6 (ite (= O 3)
                                           (@3ArrayRequest (requests L))
                                           (ite (= O 4)
                                                (@4ArrayRequest (requests L))
                                                (@defaultArrayRequest
                                                  (requests L)))))
                                 (a!13 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (wd_location H)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (wd_location H)))))
                                 (a!14 (SomeOrigin (TupleOrigin (url_protocol (wd_location H))
                                                                (url_host (wd_location H))
                                                                (url_port (wd_location H)))))
                                 (a!15 (OpaqueOrigin (@0url_path_data (url_path (wd_location H)))))
                                 (a!17 (SomeOrigin (@0url_path_blob (url_path (wd_location H)))))
                                 (a!21 (@0ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!22 (@1ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!23 (@2ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!24 (@3ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!25 (@4ArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!26 (@defaultArrayoptionDOMElement
                                         (dm_body (dc_dom (wd_document H)))))
                                 (a!32 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url E)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url E)))))
                                 (a!33 (ite (= D 3)
                                            (@3ArrayResponse (responses L))
                                            (ite (= D 4)
                                                 (@4ArrayResponse (responses L))
                                                 (@defaultArrayResponse
                                                   (responses L))))))
                           (let ((a!2 (ite (= O 3)
                                           (Build_ArrayoptionInt
                                             (@0ArrayoptionInt (wk_cache N))
                                             (@1ArrayoptionInt (wk_cache N))
                                             (@2ArrayoptionInt (wk_cache N))
                                             P
                                             (@4ArrayoptionInt (wk_cache N))
                                             (@defaultArrayoptionInt
                                               (wk_cache N)))
                                           a!1))
                                 (a!7 (ite (= O 1)
                                           (@1ArrayRequest (requests L))
                                           (ite (= O 2)
                                                (@2ArrayRequest (requests L))
                                                a!6)))
                                 (a!16 (ite ((_ is url_path_data)
                                              (url_path (wd_location H)))
                                            (SomeOrigin a!15)
                                            NoneOrigin))
                                 (a!18 (ite ((_ is url_path_blob)
                                              (url_path (wd_location H)))
                                            a!17
                                            NoneOrigin))
                                 (a!27 (ite (= J 2)
                                            a!23
                                            (ite (= J 3)
                                                 a!24
                                                 (ite (= J 4) a!25 a!26))))
                                 (a!34 (ite (= D 1)
                                            (@1ArrayResponse (responses L))
                                            (ite (= D 2)
                                                 (@2ArrayResponse (responses L))
                                                 a!33))))
                           (let ((a!3 (ite (= O 2)
                                           (Build_ArrayoptionInt
                                             (@0ArrayoptionInt (wk_cache N))
                                             (@1ArrayoptionInt (wk_cache N))
                                             P
                                             (@3ArrayoptionInt (wk_cache N))
                                             (@4ArrayoptionInt (wk_cache N))
                                             (@defaultArrayoptionInt
                                               (wk_cache N)))
                                           a!2))
                                 (a!8 (rq_url (ite (= O 0)
                                                   (@0ArrayRequest (requests L))
                                                   a!7)))
                                 (a!19 (ite ((_ is url_path_data)
                                              (url_path (wd_location H)))
                                            NoneOrigin
                                            a!18))
                                 (a!28 (ite (= J 0)
                                            a!21
                                            (ite (= J 1) a!22 a!27)))
                                 (a!35 (= (ite (= D 0)
                                               (@0ArrayResponse (responses L))
                                               a!34)
                                          E)))
                           (let ((a!4 (ite (= O 1)
                                           (Build_ArrayoptionInt
                                             (@0ArrayoptionInt (wk_cache N))
                                             P
                                             (@2ArrayoptionInt (wk_cache N))
                                             (@3ArrayoptionInt (wk_cache N))
                                             (@4ArrayoptionInt (wk_cache N))
                                             (@defaultArrayoptionInt
                                               (wk_cache N)))
                                           a!3))
                                 (a!9 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!8)))))
                                 (a!10 (ite ((_ is url_path_blob)
                                              (url_path a!8))
                                            (SomeOrigin (@0url_path_blob (url_path a!8)))
                                            NoneOrigin))
                                 (a!20 (ite ((_ is ProtocolData)
                                              (url_protocol (wd_location H)))
                                            a!16
                                            a!19))
                                 (a!29 (not ((_ is ContentElementHTML)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!28)))))
                                 (a!30 (not ((_ is ContentElementImage)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!28)))))
                                 (a!31 (= (@0ContentElementScript
                                            (@1DOMElementResource
                                              (@0SomeDOMElement a!28)))
                                          K))
                                 (a!36 (or (= P NoneInt)
                                           (and (= a!8 (rp_url E))
                                                (= P (SomeInt D))
                                                a!35))))
                           (let ((a!5 (ite (= O 0)
                                           (Build_ArrayoptionInt
                                             P
                                             (@1ArrayoptionInt (wk_cache N))
                                             (@2ArrayoptionInt (wk_cache N))
                                             (@3ArrayoptionInt (wk_cache N))
                                             (@4ArrayoptionInt (wk_cache N))
                                             (@defaultArrayoptionInt
                                               (wk_cache N)))
                                           a!4))
                                 (a!11 (ite ((_ is ProtocolData)
                                              (url_protocol a!8))
                                            (ite ((_ is url_path_data)
                                                   (url_path a!8))
                                                 a!9
                                                 NoneOrigin)
                                            (ite ((_ is url_path_data)
                                                   (url_path a!8))
                                                 NoneOrigin
                                                 a!10))))
                           (let ((a!12 (ite (or ((_ is ProtocolHTTPS)
                                                  (url_protocol a!8))
                                                ((_ is ProtocolHTTP)
                                                  (url_protocol a!8)))
                                            (SomeOrigin (TupleOrigin (url_protocol a!8)
                                                                     (url_host a!8)
                                                                     (url_port a!8)))
                                            a!11)))
                           (let ((a!37 (and (Reachable L Q A)
                                            (= T
                                               (Build_ServiceWorker (+ 1 R) a!5))
                                            (= A (Build_State R S N H U V W))
                                            (= B
                                               (Build_State (+ 1 R) S T H U V W))
                                            (= (url_protocol (wd_location H))
                                               ProtocolHTTPS)
                                            (= a!12 (ite a!13 a!14 a!20))
                                            (not (= a!12 NoneOrigin))
                                            (= F (DOMPath nilInt M))
                                            (= F (DOMPath nilInt G))
                                            (= F (DOMPath I (DOMIndex J)))
                                            ((_ is SomeDOMElement) a!28)
                                            (not ((_ is DOMElementForm)
                                                   (@0SomeDOMElement a!28)))
                                            a!29
                                            a!30
                                            ((_ is ContentElementScript)
                                              (@1DOMElementResource
                                                (@0SomeDOMElement a!28)))
                                            a!31
                                            (c_script_update_cache (config L))
                                            a!32
                                            a!36
                                            (= C
                                               (consEvent (EvScriptUpdateCache
                                                            F
                                                            O
                                                            P)
                                                          Q)))))
                             (=> a!37 (Reachable L C B)))))))))
                           :weight 0))))
      (a!100 (asserted (forall ((A State)
                                (B State)
                                (C listEvent)
                                (D Int)
                                (E Origin)
                                (F Origin)
                                (G optionCSP)
                                (H NestedDOMPath)
                                (I ArrayoptionBlob)
                                (J Global)
                                (K Int)
                                (L FetchEngine)
                                (M Window)
                                (N Int)
                                (O DOMSelector)
                                (P Response)
                                (Q Window)
                                (R listInt)
                                (S DOMSelector)
                                (T Int)
                                (U listEvent)
                                (V ServiceWorker)
                                (W ArrayoptionSetCookie)
                                (X ArrayoptionBlob)
                                (Y ArrayoptionStorageItem))
                         (! (let ((a!1 (not (= (rp_hd_content_type
                                                 (rp_headers P))
                                               NoneContentType)))
                                  (a!2 (ite (= K 3)
                                            (@3ArrayWindow (windows J))
                                            (ite (= K 4)
                                                 (@4ArrayWindow (windows J))
                                                 (@defaultArrayWindow
                                                   (windows J)))))
                                  (a!5 (or ((_ is ProtocolHTTPS)
                                             (url_protocol (rp_url P)))
                                           ((_ is ProtocolHTTP)
                                             (url_protocol (rp_url P)))
                                           (= (rp_hd_csp (rp_headers P))
                                              NoneCSP)))
                                  (a!6 (html_body (@0ContentElementHTML
                                                    (@0SomeContentElement
                                                      (rp_content P)))))
                                  (a!28 (@0SomeCSP (rp_hd_csp (dc_headers (wd_document Q)))))
                                  (a!29 ((_ is SomeCSP)
                                          (rp_hd_csp (dc_headers (wd_document Q)))))
                                  (a!30 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location Q)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location Q)))))
                                  (a!31 (SomeOrigin (TupleOrigin (url_protocol (wd_location Q))
                                                                 (url_host (wd_location Q))
                                                                 (url_port (wd_location Q)))))
                                  (a!32 (OpaqueOrigin (@0url_path_data (url_path (wd_location Q)))))
                                  (a!34 (SomeOrigin (@0url_path_blob (url_path (wd_location Q)))))
                                  (a!38 (script_src (@0ContentElementScript
                                                      (@0SomeContentElement
                                                        (rp_content P)))))
                                  (a!68 (script_nonce (@0ContentElementScript
                                                        (@0SomeContentElement
                                                          (rp_content P)))))
                                  (a!69 (@0ArrayoptionInt (in_body (dc_init (wd_document Q)))))
                                  (a!70 (@1ArrayoptionInt (in_body (dc_init (wd_document Q)))))
                                  (a!71 (@2ArrayoptionInt (in_body (dc_init (wd_document Q)))))
                                  (a!72 (@3ArrayoptionInt (in_body (dc_init (wd_document Q)))))
                                  (a!73 (@4ArrayoptionInt (in_body (dc_init (wd_document Q)))))
                                  (a!74 (@defaultArrayoptionInt
                                          (in_body (dc_init (wd_document Q)))))
                                  (a!82 (= (rp_hd_csp (rp_headers P))
                                           (rp_hd_csp (dc_headers (wd_document M)))))
                                  (a!84 (= (@1url_path_blob (url_path (rp_url P)))
                                           0))
                                  (a!85 (= (@1url_path_blob (url_path (rp_url P)))
                                           1))
                                  (a!86 (= (@1url_path_blob (url_path (rp_url P)))
                                           2))
                                  (a!87 (= (@1url_path_blob (url_path (rp_url P)))
                                           3))
                                  (a!88 (= (@1url_path_blob (url_path (rp_url P)))
                                           4))
                                  (a!96 (frame_window (@0ContentElementFrame
                                                        (@0SomeContentElement
                                                          (rp_content P)))))
                                  (a!99 (html_body (@1ContentElementFrame
                                                     (@0SomeContentElement
                                                       (rp_content P)))))
                                  (a!123 (@0ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!124 (@1ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!125 (@2ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!126 (@3ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!127 (@4ArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!128 (@defaultArrayoptionHTMLElement
                                           (html_body (dc_html (wd_document Q)))))
                                  (a!132 (image_src (@0ContentElementImage
                                                      (@0SomeContentElement
                                                        (rp_content P)))))
                                  (a!133 (frame_src (@0ContentElementFrame
                                                      (@0SomeContentElement
                                                        (rp_content P)))))
                                  (a!136 (not ((_ is ContentElementHTML)
                                                (@0SomeContentElement
                                                  (rp_content P)))))
                                  (a!137 (SomeDOMElement (DOMElementResource
                                                           (rp_url P)
                                                           (@0SomeContentElement
                                                             (rp_content P)))))
                                  (a!138 (@1ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!139 (@2ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!140 (@3ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!141 (@4ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!142 (@defaultArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!143 (@0ArrayoptionDOMElement
                                           (dm_body (dc_dom (wd_document Q)))))
                                  (a!150 (not ((_ is SomeContentType)
                                                (rp_hd_content_type
                                                  (rp_headers P)))))
                                  (a!154 (ite ((_ is ContentElementScript)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              ContentTypeScript
                                              ContentTypeHTML))
                                  (a!159 (ite ((_ is EmitterScript)
                                                (ft_emitter L))
                                              (not (= O DOMTopLevel))
                                              (and ((_ is EmitterForm)
                                                     (ft_emitter L))
                                                   (= O DOMTopLevel))))
                                  (a!160 (or ((_ is ProtocolHTTPS)
                                               (url_protocol (rp_url P)))
                                             ((_ is ProtocolHTTP)
                                               (url_protocol (rp_url P)))))
                                  (a!161 (SomeOrigin (TupleOrigin (url_protocol (rp_url P))
                                                                  (url_host (rp_url P))
                                                                  (url_port (rp_url P)))))
                                  (a!162 (OpaqueOrigin (@0url_path_data (url_path (rp_url P)))))
                                  (a!164 (SomeOrigin (@0url_path_blob (url_path (rp_url P)))))
                                  (a!168 (ite (= D 3)
                                              (@3ArrayprodOriginoptionCSP
                                                (origin_csp J))
                                              (ite (= D 4)
                                                   (@4ArrayprodOriginoptionCSP
                                                     (origin_csp J))
                                                   (@defaultArrayprodOriginoptionCSP
                                                     (origin_csp J)))))
                                  (a!173 (not ((_ is SomeURL)
                                                (rp_hd_location (rp_headers P)))))
                                  (a!175 (or (and (= S DOMTopLevel)
                                                  (= X
                                                     (Build_ArrayoptionBlob
                                                       NoneBlob
                                                       NoneBlob
                                                       NoneBlob
                                                       NoneBlob
                                                       NoneBlob
                                                       NoneBlob)))
                                             (and (= S (DOMIndex T)) (= X I)))))
                            (let ((a!3 (ite (= K 1)
                                            (@1ArrayWindow (windows J))
                                            (ite (= K 2)
                                                 (@2ArrayWindow (windows J))
                                                 a!2)))
                                  (a!7 (or ((_ is HTMLScript)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!6)))
                                           ((_ is HTMLImage)
                                             (@0SomeHTMLElement
                                               (@0ArrayoptionHTMLElement a!6)))))
                                  (a!8 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!6)))
                                                   (@1HTMLForm (@0SomeHTMLElement
                                                                 (@0ArrayoptionHTMLElement
                                                                   a!6)))))
                                  (a!10 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!6)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@1ArrayoptionHTMLElement a!6)))))
                                  (a!11 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!6)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@1ArrayoptionHTMLElement
                                                                    a!6)))))
                                  (a!13 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!6)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@2ArrayoptionHTMLElement a!6)))))
                                  (a!14 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!6)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@2ArrayoptionHTMLElement
                                                                    a!6)))))
                                  (a!16 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!6)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@3ArrayoptionHTMLElement a!6)))))
                                  (a!17 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!6)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@3ArrayoptionHTMLElement
                                                                    a!6)))))
                                  (a!19 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!6)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@4ArrayoptionHTMLElement a!6)))))
                                  (a!20 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!6)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@4ArrayoptionHTMLElement
                                                                    a!6)))))
                                  (a!22 (or ((_ is HTMLScript)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!6)))
                                            ((_ is HTMLImage)
                                              (@0SomeHTMLElement
                                                (@defaultArrayoptionHTMLElement
                                                  a!6)))))
                                  (a!23 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!6)))
                                                    (@1HTMLForm (@0SomeHTMLElement
                                                                  (@defaultArrayoptionHTMLElement
                                                                    a!6)))))
                                  (a!33 (ite ((_ is url_path_data)
                                               (url_path (wd_location Q)))
                                             (SomeOrigin a!32)
                                             NoneOrigin))
                                  (a!35 (ite ((_ is url_path_blob)
                                               (url_path (wd_location Q)))
                                             a!34
                                             NoneOrigin))
                                  (a!39 (SomeOrigin (OpaqueOrigin (@0url_path_data (url_path a!38)))))
                                  (a!40 (ite ((_ is url_path_blob)
                                               (url_path a!38))
                                             (SomeOrigin (@0url_path_blob (url_path a!38)))
                                             NoneOrigin))
                                  (a!44 (= (url_protocol a!38)
                                           (@0CSPSrcScheme (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!45 ((_ is SomePath)
                                          (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!46 (@0SomePath (@4CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!48 ((_ is SomeInt)
                                          (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!49 (@0SomeInt (@3CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!50 (= (@0domain (@0SomeDomain (url_host a!38)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!51 (= (@1subdomain (@0SomeDomain (url_host a!38)))
                                           (@2CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!53 ((_ is SomeProtocol)
                                          (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!54 (@0SomeProtocol (@0CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!57 ((_ is SomeoptionInt)
                                          (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!58 (@0SomeoptionInt (@1CSPSrcSource (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!60 (not ((_ is domain)
                                               (@0SomeDomain (url_host a!38)))))
                                  (a!62 (and ((_ is SomeDomain) (url_host a!38))
                                             ((_ is domain)
                                               (@0SomeDomain (url_host a!38)))))
                                  (a!66 (not ((_ is CSPSrcNone)
                                               (@0SomeCSPSrc (csp_script_src a!28)))))
                                  (a!75 (ite (= (@0DOMIndex O) 3)
                                             a!72
                                             (ite (= (@0DOMIndex O) 4)
                                                  a!73
                                                  a!74)))
                                  (a!89 (ite a!86
                                             (@2ArrayoptionBlob I)
                                             (ite a!87
                                                  (@3ArrayoptionBlob I)
                                                  (ite a!88
                                                       (@4ArrayoptionBlob I)
                                                       (@defaultArrayoptionBlob
                                                         I)))))
                                  (a!97 (ite (= a!96 3)
                                             (@3ArrayWindow (windows J))
                                             (ite (= a!96 4)
                                                  (@4ArrayWindow (windows J))
                                                  (@defaultArrayWindow
                                                    (windows J)))))
                                  (a!100 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@0ArrayoptionHTMLElement a!99)))))
                                  (a!101 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@0ArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@0ArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!103 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement a!99)))))
                                  (a!104 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@1ArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@1ArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!106 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement a!99)))))
                                  (a!107 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@2ArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@2ArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!109 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement a!99)))))
                                  (a!110 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@3ArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@3ArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!112 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement a!99)))))
                                  (a!113 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@4ArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@4ArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!115 (or ((_ is HTMLScript)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!99)))
                                             ((_ is HTMLImage)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!99)))))
                                  (a!116 (Build_Form (@0HTMLForm (@0SomeHTMLElement
                                                                   (@defaultArrayoptionHTMLElement
                                                                     a!99)))
                                                     (@1HTMLForm (@0SomeHTMLElement
                                                                   (@defaultArrayoptionHTMLElement
                                                                     a!99)))))
                                  (a!129 (ite (= (@0DOMIndex O) 3)
                                              a!126
                                              (ite (= (@0DOMIndex O) 4)
                                                   a!127
                                                   a!128)))
                                  (a!144 (ite (= (@0DOMIndex O) 4)
                                              (Build_ArrayoptionDOMElement
                                                a!143
                                                a!138
                                                a!139
                                                a!140
                                                a!137
                                                a!142)
                                              (dm_body (dc_dom (wd_document Q)))))
                                  (a!151 (ite ((_ is ContentElementScript)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              (= a!38 (rp_url P))
                                              (= a!133 (rp_url P))))
                                  (a!155 (ite ((_ is ContentElementImage)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              ContentTypeImage
                                              a!154))
                                  (a!163 (ite ((_ is url_path_data)
                                                (url_path (rp_url P)))
                                              (SomeOrigin a!162)
                                              NoneOrigin))
                                  (a!165 (ite ((_ is url_path_blob)
                                                (url_path (rp_url P)))
                                              a!164
                                              NoneOrigin))
                                  (a!169 (ite (= D 1)
                                              (@1ArrayprodOriginoptionCSP
                                                (origin_csp J))
                                              (ite (= D 2)
                                                   (@2ArrayprodOriginoptionCSP
                                                     (origin_csp J))
                                                   a!168)))
                                  (a!174 (and a!173
                                              (not ((_ is ResponseNoContent)
                                                     (rp_code P))))))
                            (let ((a!4 (= (ite (= K 0)
                                               (@0ArrayWindow (windows J))
                                               a!3)
                                          M))
                                  (a!9 (ite ((_ is HTMLForm)
                                              (@0SomeHTMLElement
                                                (@0ArrayoptionHTMLElement a!6)))
                                            (SomeDOMElement (DOMElementForm a!8))
                                            NoneDOMElement))
                                  (a!12 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@1ArrayoptionHTMLElement a!6)))
                                             (SomeDOMElement (DOMElementForm a!11))
                                             NoneDOMElement))
                                  (a!15 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@2ArrayoptionHTMLElement a!6)))
                                             (SomeDOMElement (DOMElementForm a!14))
                                             NoneDOMElement))
                                  (a!18 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@3ArrayoptionHTMLElement a!6)))
                                             (SomeDOMElement (DOMElementForm a!17))
                                             NoneDOMElement))
                                  (a!21 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@4ArrayoptionHTMLElement a!6)))
                                             (SomeDOMElement (DOMElementForm a!20))
                                             NoneDOMElement))
                                  (a!24 (ite ((_ is HTMLForm)
                                               (@0SomeHTMLElement
                                                 (@defaultArrayoptionHTMLElement
                                                   a!6)))
                                             (SomeDOMElement (DOMElementForm a!23))
                                             NoneDOMElement))
                                  (a!36 (ite ((_ is url_path_data)
                                               (url_path (wd_location Q)))
                                             NoneOrigin
                                             a!35))
                                  (a!41 (ite ((_ is ProtocolData)
                                               (url_protocol a!38))
                                             (ite ((_ is url_path_data)
                                                    (url_path a!38))
                                                  a!39
                                                  NoneOrigin)
                                             (ite ((_ is url_path_data)
                                                    (url_path a!38))
                                                  NoneOrigin
                                                  a!40)))
                                  (a!47 (and (not ((_ is url_path_blob)
                                                    (url_path a!38)))
                                             (not ((_ is url_path_data)
                                                    (url_path a!38)))
                                             (= (@0url_path_res (url_path a!38))
                                                a!46)))
                                  (a!52 (ite ((_ is domain)
                                               (@0SomeDomain (url_host a!38)))
                                             a!50
                                             a!51))
                                  (a!59 (= (@0subdomain (@0SomeDomain (url_host a!38)))
                                           (@0SomeInt a!58)))
                                  (a!76 (ite (= (@0DOMIndex O) 1)
                                             a!70
                                             (ite (= (@0DOMIndex O) 2)
                                                  a!71
                                                  a!75)))
                                  (a!90 (@0SomeBlob (ite a!84
                                                         (@0ArrayoptionBlob I)
                                                         (ite a!85
                                                              (@1ArrayoptionBlob
                                                                I)
                                                              a!89))))
                                  (a!92 ((_ is SomeBlob)
                                          (ite a!84
                                               (@0ArrayoptionBlob I)
                                               (ite a!85
                                                    (@1ArrayoptionBlob I)
                                                    a!89))))
                                  (a!98 (ite (= a!96 1)
                                             (@1ArrayWindow (windows J))
                                             (ite (= a!96 2)
                                                  (@2ArrayWindow (windows J))
                                                  a!97)))
                                  (a!102 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@0ArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!101))
                                              NoneDOMElement))
                                  (a!105 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@1ArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!104))
                                              NoneDOMElement))
                                  (a!108 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@2ArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!107))
                                              NoneDOMElement))
                                  (a!111 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@3ArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!110))
                                              NoneDOMElement))
                                  (a!114 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@4ArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!113))
                                              NoneDOMElement))
                                  (a!117 (ite ((_ is HTMLForm)
                                                (@0SomeHTMLElement
                                                  (@defaultArrayoptionHTMLElement
                                                    a!99)))
                                              (SomeDOMElement (DOMElementForm a!116))
                                              NoneDOMElement))
                                  (a!130 (ite (= (@0DOMIndex O) 1)
                                              a!124
                                              (ite (= (@0DOMIndex O) 2)
                                                   a!125
                                                   a!129)))
                                  (a!145 (ite (= (@0DOMIndex O) 2)
                                              (Build_ArrayoptionDOMElement
                                                a!143
                                                a!138
                                                a!137
                                                a!140
                                                a!141
                                                a!142)
                                              (ite (= (@0DOMIndex O) 3)
                                                   (Build_ArrayoptionDOMElement
                                                     a!143
                                                     a!138
                                                     a!139
                                                     a!137
                                                     a!141
                                                     a!142)
                                                   a!144)))
                                  (a!152 (ite ((_ is ContentElementImage)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              (= a!132 (rp_url P))
                                              a!151))
                                  (a!156 (ite ((_ is ContentElementHTML)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              ContentTypeHTML
                                              a!155))
                                  (a!166 (ite ((_ is url_path_data)
                                                (url_path (rp_url P)))
                                              NoneOrigin
                                              a!165))
                                  (a!170 (= (ite (= D 0)
                                                 (@0ArrayprodOriginoptionCSP
                                                   (origin_csp J))
                                                 a!169)
                                            (pairOriginoptionCSP E G))))
                            (let ((a!25 (Build_ArrayoptionDOMElement
                                          (ite ((_ is SomeHTMLElement)
                                                 (@0ArrayoptionHTMLElement a!6))
                                               (ite a!7 NoneDOMElement a!9)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@1ArrayoptionHTMLElement a!6))
                                               (ite a!10 NoneDOMElement a!12)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@2ArrayoptionHTMLElement a!6))
                                               (ite a!13 NoneDOMElement a!15)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@3ArrayoptionHTMLElement a!6))
                                               (ite a!16 NoneDOMElement a!18)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@4ArrayoptionHTMLElement a!6))
                                               (ite a!19 NoneDOMElement a!21)
                                               NoneDOMElement)
                                          (ite ((_ is SomeHTMLElement)
                                                 (@defaultArrayoptionHTMLElement
                                                   a!6))
                                               (ite a!22 NoneDOMElement a!24)
                                               NoneDOMElement)))
                                  (a!37 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location Q)))
                                             a!33
                                             a!36))
                                  (a!42 (ite (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!38))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!38)))
                                             (SomeOrigin (TupleOrigin (url_protocol a!38)
                                                                      (url_host a!38)
                                                                      (url_port a!38)))
                                             a!41))
                                  (a!61 (ite ((_ is SomeInt) a!58)
                                             (and a!59
                                                  ((_ is SomeDomain)
                                                    (url_host a!38))
                                                  a!60)
                                             (and ((_ is SomeDomain)
                                                    (url_host a!38))
                                                  a!60)))
                                  (a!77 ((_ is SomeInt)
                                          (ite (= (@0DOMIndex O) 0) a!69 a!76)))
                                  (a!78 (@0SomeInt (ite (= (@0DOMIndex O) 0)
                                                        a!69
                                                        a!76)))
                                  (a!118 (Build_ArrayoptionDOMElement
                                           (ite ((_ is SomeHTMLElement)
                                                  (@0ArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!100 NoneDOMElement a!102)
                                                NoneDOMElement)
                                           (ite ((_ is SomeHTMLElement)
                                                  (@1ArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!103 NoneDOMElement a!105)
                                                NoneDOMElement)
                                           (ite ((_ is SomeHTMLElement)
                                                  (@2ArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!106 NoneDOMElement a!108)
                                                NoneDOMElement)
                                           (ite ((_ is SomeHTMLElement)
                                                  (@3ArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!109 NoneDOMElement a!111)
                                                NoneDOMElement)
                                           (ite ((_ is SomeHTMLElement)
                                                  (@4ArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!112 NoneDOMElement a!114)
                                                NoneDOMElement)
                                           (ite ((_ is SomeHTMLElement)
                                                  (@defaultArrayoptionHTMLElement
                                                    a!99))
                                                (ite a!115 NoneDOMElement a!117)
                                                NoneDOMElement)))
                                  (a!131 (@0SomeHTMLElement
                                           (ite (= (@0DOMIndex O) 0)
                                                a!123
                                                a!130)))
                                  (a!146 (ite (= (@0DOMIndex O) 0)
                                              (Build_ArrayoptionDOMElement
                                                a!137
                                                a!138
                                                a!139
                                                a!140
                                                a!141
                                                a!142)
                                              (ite (= (@0DOMIndex O) 1)
                                                   (Build_ArrayoptionDOMElement
                                                     a!143
                                                     a!137
                                                     a!139
                                                     a!140
                                                     a!141
                                                     a!142)
                                                   a!145)))
                                  (a!149 ((_ is SomeHTMLElement)
                                           (ite (= (@0DOMIndex O) 0)
                                                a!123
                                                a!130)))
                                  (a!153 (or ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content P)))
                                             a!152))
                                  (a!157 (= a!156
                                            (@0SomeContentType
                                              (rp_hd_content_type
                                                (rp_headers P)))))
                                  (a!167 (ite ((_ is ProtocolData)
                                                (url_protocol (rp_url P)))
                                              a!163
                                              a!166)))
                            (let ((a!26 (Build_Document (+ 1 N)
                                                        (ft_correlator L)
                                                        (rp_headers P)
                                                        (@0ContentElementHTML
                                                          (@0SomeContentElement
                                                            (rp_content P)))
                                                        (Build_DOM (ft_correlator L)
                                                                   0
                                                                   a!25)
                                                        (Build_Initiators NoneInt
                                                                          (Build_ArrayoptionInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt
                                                                            NoneInt))))
                                  (a!43 (= (SomeOrigin (@0SomeOrigin (ite a!30
                                                                          a!31
                                                                          a!37)))
                                           a!42))
                                  (a!55 (not ((_ is TupleOrigin)
                                               (@0SomeOrigin (ite a!30
                                                                  a!31
                                                                  a!37)))))
                                  (a!56 (= (url_protocol a!38)
                                           (@0TupleOrigin (@0SomeOrigin (ite a!30
                                                                             a!31
                                                                             a!37)))))
                                  (a!79 (ite (= a!78 3)
                                             (@3ArrayWindow (windows J))
                                             (ite (= a!78 4)
                                                  (@4ArrayWindow (windows J))
                                                  (@defaultArrayWindow
                                                    (windows J)))))
                                  (a!119 (Build_Document (+ 1 N)
                                                         (ft_correlator L)
                                                         (rp_headers P)
                                                         (@1ContentElementFrame
                                                           (@0SomeContentElement
                                                             (rp_content P)))
                                                         (Build_DOM (ft_correlator L)
                                                                    0
                                                                    a!118)
                                                         (Build_Initiators NoneInt
                                                                           (Build_ArrayoptionInt
                                                                             NoneInt
                                                                             NoneInt
                                                                             NoneInt
                                                                             NoneInt
                                                                             NoneInt
                                                                             NoneInt))))
                                  (a!134 (ite ((_ is ContentElementScript)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              (= a!131 (HTMLScript a!38))
                                              (= a!131 (HTMLFrame a!133))))
                                  (a!147 (Build_DOM (dm_nonce (dc_dom (wd_document Q)))
                                                    (dm_head (dc_dom (wd_document Q)))
                                                    a!146))
                                  (a!158 (or (not ((_ is SomeContentElement)
                                                    (rp_content P)))
                                             a!150
                                             (and a!153 a!157)))
                                  (a!171 (and (c_origin_wide_csp (config J))
                                              (= (ite a!160 a!161 a!167)
                                                 (SomeOrigin F))
                                              a!170
                                              (= E F)
                                              (= (rp_hd_csp (rp_headers P)) G))))
                            (let ((a!27 (and a!5
                                             ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content P)))
                                             (= M
                                                (Build_Window (ft_correlator L)
                                                              NoneInt
                                                              (rp_url P)
                                                              NoneDomain
                                                              a!26))))
                                  (a!63 (and (or (not a!45) a!47)
                                             (or (not a!48)
                                                 (= (url_port a!38)
                                                    (SomeInt a!49)))
                                             a!52
                                             (ite a!53
                                                  (= (url_protocol a!38) a!54)
                                                  (or a!55 a!56))
                                             (ite a!57 a!61 a!62)
                                             ((_ is SomeDomain) (url_host a!38))))
                                  (a!80 (ite (= a!78 1)
                                             (@1ArrayWindow (windows J))
                                             (ite (= a!78 2)
                                                  (@2ArrayWindow (windows J))
                                                  a!79)))
                                  (a!120 (= (ite (= a!96 0)
                                                 (@0ArrayWindow (windows J))
                                                 a!98)
                                            (Build_Window (ft_correlator L)
                                                          (SomeInt K)
                                                          (rp_url P)
                                                          NoneDomain
                                                          a!119)))
                                  (a!135 (ite ((_ is ContentElementImage)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              (= a!131 (HTMLImage a!132))
                                              a!134))
                                  (a!148 (Build_Window (wd_nonce Q)
                                                       (wd_parent Q)
                                                       (wd_location Q)
                                                       (wd_document_domain Q)
                                                       (Build_Document (+ 1 N)
                                                                       (dc_nonce (wd_document Q))
                                                                       (dc_headers (wd_document Q))
                                                                       (dc_html (wd_document Q))
                                                                       a!147
                                                                       (dc_init (wd_document Q)))))
                                  (a!172 (or (not (c_origin_wide_csp (config J)))
                                             a!171)))
                            (let ((a!64 (ite ((_ is CSPSrcScheme)
                                               (@0SomeCSPSrc (csp_script_src a!28)))
                                             a!44
                                             a!63))
                                  (a!81 (wd_document (ite (= a!78 0)
                                                          (@0ArrayWindow (windows J))
                                                          a!80))))
                            (let ((a!65 (ite ((_ is CSPSrcSelf)
                                               (@0SomeCSPSrc (csp_script_src a!28)))
                                             a!43
                                             a!64))
                                  (a!83 (ite (c_csp_inherit_local_from_initiator
                                               (config J))
                                             (= (rp_hd_csp (rp_headers P))
                                                (rp_hd_csp (dc_headers a!81)))
                                             a!82)))
                            (let ((a!67 (or (not ((_ is SomeCSPSrc)
                                                   (csp_script_src a!28)))
                                            (not a!29)
                                            (and a!65
                                                 ((_ is SomeOrigin)
                                                   (ite a!30 a!31 a!37))
                                                 a!66)))
                                  (a!91 (ite (c_csp_inherit_blob_from_creator
                                               (config J))
                                             (= (rp_hd_csp (rp_headers P))
                                                (blob_csp a!90))
                                             (ite a!77 a!83 a!82))))
                            (let ((a!93 (ite ((_ is url_path_blob)
                                               (url_path (rp_url P)))
                                             (and a!91 a!92)
                                             (ite a!77 a!83 a!82))))
                            (let ((a!94 (ite ((_ is url_path_data)
                                               (url_path (rp_url P)))
                                             (ite a!77 a!83 a!82)
                                             a!93)))
                            (let ((a!95 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (rp_url P)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (rp_url P)))
                                            a!94)))
                            (let ((a!121 (ite ((_ is ContentElementScript)
                                                (@0SomeContentElement
                                                  (rp_content P)))
                                              (and a!67 (= a!68 N))
                                              (and a!95 a!120))))
                            (let ((a!122 (or ((_ is ContentElementHTML)
                                               (@0SomeContentElement
                                                 (rp_content P)))
                                             ((_ is ContentElementImage)
                                               (@0SomeContentElement
                                                 (rp_content P)))
                                             a!121)))
                            (let ((a!176 (and (Reachable J U A)
                                              (= A (Build_State N L V Q W I Y))
                                              (= B
                                                 (Build_State (+ 1 N)
                                                              L
                                                              V
                                                              M
                                                              W
                                                              X
                                                              Y))
                                              a!1
                                              ((_ is SomeContentElement)
                                                (rp_content P))
                                              (= (rp_code P) ResponseOk)
                                              (= (ft_response L)
                                                 (SomeResponse P))
                                              (= H (DOMPath nilInt O))
                                              (= H (DOMPath R S))
                                              a!4
                                              (ite ((_ is DOMTopLevel) O)
                                                   a!27
                                                   (and a!122
                                                        a!135
                                                        a!136
                                                        (= M a!148)
                                                        a!149))
                                              a!158
                                              (or ((_ is EmitterClient)
                                                    (ft_emitter L))
                                                  a!159)
                                              a!172
                                              (or ((_ is ResponseOk)
                                                    (rp_code P))
                                                  a!174)
                                              a!175
                                              (= C
                                                 (consEvent (EvDOMUpdate H) U)))))
                              (=> a!176 (Reachable J C B)))))))))))))))))
                            :weight 0))))
      (a!103 (asserted (forall ((A Script)
                                (B NestedDOMPath)
                                (C Window)
                                (D Global)
                                (E Global)
                                (F NestedDOMPath)
                                (G DOMSelector)
                                (H Window)
                                (I Window)
                                (J NestedDOMPath)
                                (K listInt)
                                (L Int)
                                (M Window)
                                (N Script)
                                (O Form)
                                (P NestedDOMPath)
                                (Q Window)
                                (R Global)
                                (S Global)
                                (T NestedDOMPath)
                                (U DOMSelector)
                                (V Window)
                                (W Window)
                                (X NestedDOMPath)
                                (Y listInt)
                                (Z Int)
                                (A1 Window)
                                (B1 Form)
                                (C1 Request)
                                (D1 Int)
                                (E1 Script)
                                (F1 NestedDOMPath)
                                (G1 Window)
                                (H1 Global)
                                (I1 Global)
                                (J1 NestedDOMPath)
                                (K1 DOMSelector)
                                (L1 Window)
                                (M1 Window)
                                (N1 NestedDOMPath)
                                (O1 listInt)
                                (P1 Int)
                                (Q1 Window)
                                (R1 Script)
                                (S1 Global)
                                (T1 Window)
                                (U1 Window)
                                (V1 State)
                                (W1 State)
                                (X1 listEvent)
                                (Y1 Int)
                                (Z1 Int)
                                (A2 Int)
                                (B2 Origin)
                                (C2 Blob)
                                (D2 Int)
                                (E2 Int)
                                (F2 Int)
                                (G2 Origin)
                                (H2 Blob)
                                (I2 Int)
                                (J2 Int)
                                (K2 FetchEngine)
                                (L2 Int)
                                (M2 SetCookie)
                                (N2 ArrayoptionSetCookie)
                                (O2 ArrayoptionSetCookie)
                                (P2 listEvent)
                                (Q2 Int)
                                (R2 ServiceWorker)
                                (S2 ArrayoptionSetCookie)
                                (T2 ArrayoptionBlob)
                                (U2 ArrayoptionStorageItem))
                         (! (let ((a!1 (ite (= J2 3)
                                            (@3ArrayResponse (responses S1))
                                            (ite (= J2 4)
                                                 (@4ArrayResponse (responses S1))
                                                 (@defaultArrayResponse
                                                   (responses S1)))))
                                  (a!5 (SomeprodprodEmitterIntInt
                                         (pairprodEmitterIntInt
                                           (pairEmitterInt (ft_emitter K2) I2)
                                           J2)))
                                  (a!13 (ite (= I2 3)
                                             (@3ArrayRequest (requests S1))
                                             (ite (= I2 4)
                                                  (@4ArrayRequest (requests S1))
                                                  (@defaultArrayRequest
                                                    (requests S1)))))
                                  (a!16 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!17 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!18 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!19 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!20 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!21 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document A1)))))
                                  (a!25 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!26 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!27 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!28 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!29 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!30 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document M)))))
                                  (a!37 (@0ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!38 (@1ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!39 (@2ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!40 (@3ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!41 (@4ArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!42 (@defaultArrayoptionDOMElement
                                          (dm_body (dc_dom (wd_document Q1)))))
                                  (a!48 (ite (= D1 3)
                                             (@3ArrayEmitter (emitters S1))
                                             (ite (= D1 4)
                                                  (@4ArrayEmitter (emitters S1))
                                                  (@defaultArrayEmitter
                                                    (emitters S1)))))
                                  (a!54 (ite (= I2 3)
                                             (@3ArrayInt (server_responses S1))
                                             (ite (= I2 4)
                                                  (@4ArrayInt (server_responses S1))
                                                  (@defaultArrayInt (server_responses S1)))))
                                  (a!67 (ite (= D2 3)
                                             (@3ArrayContentElement
                                               (data_urls S1))
                                             (ite (= D2 4)
                                                  (@4ArrayContentElement
                                                    (data_urls S1))
                                                  (@defaultArrayContentElement
                                                    (data_urls S1)))))
                                  (a!70 (ite (= F2 2)
                                             (@2ArrayoptionBlob T2)
                                             (ite (= F2 3)
                                                  (@3ArrayoptionBlob T2)
                                                  (ite (= F2 4)
                                                       (@4ArrayoptionBlob T2)
                                                       (@defaultArrayoptionBlob
                                                         T2)))))
                                  (a!76 (ite (= Y1 3)
                                             (@3ArrayContentElement
                                               (data_urls S1))
                                             (ite (= Y1 4)
                                                  (@4ArrayContentElement
                                                    (data_urls S1))
                                                  (@defaultArrayContentElement
                                                    (data_urls S1)))))
                                  (a!79 (ite (= A2 2)
                                             (@2ArrayoptionBlob T2)
                                             (ite (= A2 3)
                                                  (@3ArrayoptionBlob T2)
                                                  (ite (= A2 4)
                                                       (@4ArrayoptionBlob T2)
                                                       (@defaultArrayoptionBlob
                                                         T2)))))
                                  (a!84 (or ((_ is ProtocolHTTPS)
                                              (url_protocol (wd_location U1)))
                                            ((_ is ProtocolHTTP)
                                              (url_protocol (wd_location U1)))))
                                  (a!85 (SomeOrigin (TupleOrigin (url_protocol (wd_location U1))
                                                                 (url_host (wd_location U1))
                                                                 (url_port (wd_location U1)))))
                                  (a!86 (OpaqueOrigin (@0url_path_data (url_path (wd_location U1)))))
                                  (a!88 (SomeOrigin (@0url_path_blob (url_path (wd_location U1)))))
                                  (a!108 (ite (= L2 2)
                                              (@2ArrayoptionSetCookie N2)
                                              (ite (= L2 3)
                                                   (@3ArrayoptionSetCookie N2)
                                                   (ite (= L2 4)
                                                        (@4ArrayoptionSetCookie
                                                          N2)
                                                        (@defaultArrayoptionSetCookie
                                                          N2)))))
                                  (a!110 (ite (= L2 3)
                                              (Build_ArrayoptionSetCookie
                                                (@0ArrayoptionSetCookie N2)
                                                (@1ArrayoptionSetCookie N2)
                                                (@2ArrayoptionSetCookie N2)
                                                (SomeSetCookie M2)
                                                (@4ArrayoptionSetCookie N2)
                                                (@defaultArrayoptionSetCookie
                                                  N2))
                                              (ite (= L2 4)
                                                   (Build_ArrayoptionSetCookie
                                                     (@0ArrayoptionSetCookie N2)
                                                     (@1ArrayoptionSetCookie N2)
                                                     (@2ArrayoptionSetCookie N2)
                                                     (@3ArrayoptionSetCookie N2)
                                                     (SomeSetCookie M2)
                                                     (@defaultArrayoptionSetCookie
                                                       N2))
                                                   N2)))
                                  (a!113 (= (sc_reg_domain (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!114 (= (sc_path (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!115 (= (sc_name (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2)))
                                  (a!117 (= (sc_reg_domain (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!118 (= (sc_path (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!119 (= (sc_name (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2)))
                                  (a!121 (= (sc_reg_domain (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!122 (= (sc_path (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!123 (= (sc_name (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2)))
                                  (a!125 (= (sc_reg_domain (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!126 (= (sc_path (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!127 (= (sc_name (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2)))
                                  (a!129 (= (sc_reg_domain (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!130 (= (sc_path (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!131 (= (sc_name (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2)))
                                  (a!133 (= (sc_reg_domain (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                              O2)))
                                            (sc_reg_domain M2)))
                                  (a!134 (= (sc_path (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        O2)))
                                            (sc_path M2)))
                                  (a!135 (= (sc_name (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                        O2)))
                                            (sc_name M2))))
                            (let ((a!2 (ite (= J2 1)
                                            (@1ArrayResponse (responses S1))
                                            (ite (= J2 2)
                                                 (@2ArrayResponse (responses S1))
                                                 a!1)))
                                  (a!6 (ite (= (ft_correlator K2) 4)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              a!5
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history K2)))
                                            (ft_history K2)))
                                  (a!14 (ite (= I2 1)
                                             (@1ArrayRequest (requests S1))
                                             (ite (= I2 2)
                                                  (@2ArrayRequest (requests S1))
                                                  a!13)))
                                  (a!22 (ite (= Z 2)
                                             a!18
                                             (ite (= Z 3)
                                                  a!19
                                                  (ite (= Z 4) a!20 a!21))))
                                  (a!31 (ite (= L 2)
                                             a!27
                                             (ite (= L 3)
                                                  a!28
                                                  (ite (= L 4) a!29 a!30))))
                                  (a!43 (ite (= P1 2)
                                             a!39
                                             (ite (= P1 3)
                                                  a!40
                                                  (ite (= P1 4) a!41 a!42))))
                                  (a!49 (ite (= D1 1)
                                             (@1ArrayEmitter (emitters S1))
                                             (ite (= D1 2)
                                                  (@2ArrayEmitter (emitters S1))
                                                  a!48)))
                                  (a!55 (ite (= I2 1)
                                             (@1ArrayInt (server_responses S1))
                                             (ite (= I2 2)
                                                  (@2ArrayInt (server_responses S1))
                                                  a!54)))
                                  (a!68 (ite (= D2 1)
                                             (@1ArrayContentElement
                                               (data_urls S1))
                                             (ite (= D2 2)
                                                  (@2ArrayContentElement
                                                    (data_urls S1))
                                                  a!67)))
                                  (a!71 (= (ite (= F2 0)
                                                (@0ArrayoptionBlob T2)
                                                (ite (= F2 1)
                                                     (@1ArrayoptionBlob T2)
                                                     a!70))
                                           (SomeBlob H2)))
                                  (a!77 (ite (= Y1 1)
                                             (@1ArrayContentElement
                                               (data_urls S1))
                                             (ite (= Y1 2)
                                                  (@2ArrayContentElement
                                                    (data_urls S1))
                                                  a!76)))
                                  (a!80 (= (ite (= A2 0)
                                                (@0ArrayoptionBlob T2)
                                                (ite (= A2 1)
                                                     (@1ArrayoptionBlob T2)
                                                     a!79))
                                           (SomeBlob C2)))
                                  (a!87 (ite ((_ is url_path_data)
                                               (url_path (wd_location U1)))
                                             (SomeOrigin a!86)
                                             NoneOrigin))
                                  (a!89 (ite ((_ is url_path_blob)
                                               (url_path (wd_location U1)))
                                             a!88
                                             NoneOrigin))
                                  (a!109 (= (ite (= L2 0)
                                                 (@0ArrayoptionSetCookie N2)
                                                 (ite (= L2 1)
                                                      (@1ArrayoptionSetCookie
                                                        N2)
                                                      a!108))
                                            NoneSetCookie))
                                  (a!111 (ite (= L2 1)
                                              (Build_ArrayoptionSetCookie
                                                (@0ArrayoptionSetCookie N2)
                                                (SomeSetCookie M2)
                                                (@2ArrayoptionSetCookie N2)
                                                (@3ArrayoptionSetCookie N2)
                                                (@4ArrayoptionSetCookie N2)
                                                (@defaultArrayoptionSetCookie
                                                  N2))
                                              (ite (= L2 2)
                                                   (Build_ArrayoptionSetCookie
                                                     (@0ArrayoptionSetCookie N2)
                                                     (@1ArrayoptionSetCookie N2)
                                                     (SomeSetCookie M2)
                                                     (@3ArrayoptionSetCookie N2)
                                                     (@4ArrayoptionSetCookie N2)
                                                     (@defaultArrayoptionSetCookie
                                                       N2))
                                                   a!110)))
                                  (a!116 (ite (and a!113 a!114 a!115)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@0ArrayoptionSetCookie
                                                                                O2)))))
                                  (a!120 (ite (and a!117 a!118 a!119)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@1ArrayoptionSetCookie
                                                                                O2)))))
                                  (a!124 (ite (and a!121 a!122 a!123)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@2ArrayoptionSetCookie
                                                                                O2)))))
                                  (a!128 (ite (and a!125 a!126 a!127)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@3ArrayoptionSetCookie
                                                                                O2)))))
                                  (a!132 (ite (and a!129 a!130 a!131)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@4ArrayoptionSetCookie
                                                                                O2)))))
                                  (a!136 (ite (and a!133 a!134 a!135)
                                              NoneSetCookie
                                              (SomeSetCookie (@0SomeSetCookie (@defaultArrayoptionSetCookie
                                                                                O2))))))
                            (let ((a!3 (EvResponse (ite (= J2 0)
                                                        (@0ArrayResponse (responses S1))
                                                        a!2)
                                                   (ft_correlator K2)))
                                  (a!4 (SomeResponse (ite (= J2 0)
                                                          (@0ArrayResponse (responses S1))
                                                          a!2)))
                                  (a!7 (ite (= (ft_correlator K2) 3)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              a!5
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history K2)))
                                            a!6))
                                  (a!12 (rp_url (ite (= J2 0)
                                                     (@0ArrayResponse (responses S1))
                                                     a!2)))
                                  (a!15 (= (ft_request K2)
                                           (ite (= I2 0)
                                                (@0ArrayRequest (requests S1))
                                                a!14)))
                                  (a!23 (ite (= Z 0)
                                             a!16
                                             (ite (= Z 1) a!17 a!22)))
                                  (a!32 (ite (= L 0)
                                             a!25
                                             (ite (= L 1) a!26 a!31)))
                                  (a!44 (ite (= P1 0)
                                             a!37
                                             (ite (= P1 1) a!38 a!43)))
                                  (a!50 (= (ite (= D1 0)
                                                (@0ArrayEmitter (emitters S1))
                                                a!49)
                                           (EmitterScript F1 E1)))
                                  (a!53 (rq_url (ite (= I2 0)
                                                     (@0ArrayRequest (requests S1))
                                                     a!14)))
                                  (a!56 (= (ite (= I2 0)
                                                (@0ArrayInt (server_responses S1))
                                                a!55)
                                           0))
                                  (a!57 (= (ite (= I2 0)
                                                (@0ArrayInt (server_responses S1))
                                                a!55)
                                           1))
                                  (a!58 (= (ite (= I2 0)
                                                (@0ArrayInt (server_responses S1))
                                                a!55)
                                           2))
                                  (a!59 (= (ite (= I2 0)
                                                (@0ArrayInt (server_responses S1))
                                                a!55)
                                           3))
                                  (a!60 (= (ite (= I2 0)
                                                (@0ArrayInt (server_responses S1))
                                                a!55)
                                           4))
                                  (a!66 (rp_content (ite (= J2 0)
                                                         (@0ArrayResponse (responses S1))
                                                         a!2)))
                                  (a!69 (SomeContentElement
                                          (ite (= D2 0)
                                               (@0ArrayContentElement
                                                 (data_urls S1))
                                               a!68)))
                                  (a!74 (rp_headers (ite (= J2 0)
                                                         (@0ArrayResponse (responses S1))
                                                         a!2)))
                                  (a!75 (rp_code (ite (= J2 0)
                                                      (@0ArrayResponse (responses S1))
                                                      a!2)))
                                  (a!78 (SomeContentElement
                                          (ite (= Y1 0)
                                               (@0ArrayContentElement
                                                 (data_urls S1))
                                               a!77)))
                                  (a!90 (ite ((_ is url_path_data)
                                               (url_path (wd_location U1)))
                                             NoneOrigin
                                             a!89))
                                  (a!112 (= S2
                                            (ite (= L2 0)
                                                 (Build_ArrayoptionSetCookie
                                                   (SomeSetCookie M2)
                                                   (@1ArrayoptionSetCookie N2)
                                                   (@2ArrayoptionSetCookie N2)
                                                   (@3ArrayoptionSetCookie N2)
                                                   (@4ArrayoptionSetCookie N2)
                                                   (@defaultArrayoptionSetCookie
                                                     N2))
                                                 a!111)))
                                  (a!137 (Build_ArrayoptionSetCookie
                                           (ite ((_ is SomeSetCookie)
                                                  (@0ArrayoptionSetCookie O2))
                                                a!116
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@1ArrayoptionSetCookie O2))
                                                a!120
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@2ArrayoptionSetCookie O2))
                                                a!124
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@3ArrayoptionSetCookie O2))
                                                a!128
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@4ArrayoptionSetCookie O2))
                                                a!132
                                                NoneSetCookie)
                                           (ite ((_ is SomeSetCookie)
                                                  (@defaultArrayoptionSetCookie
                                                    O2))
                                                a!136
                                                NoneSetCookie))))
                            (let ((a!8 (ite (= (ft_correlator K2) 2)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@1ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              a!5
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history K2)))
                                            a!7))
                                  (a!24 (and ((_ is DOMElementForm)
                                               (@0SomeDOMElement a!23))
                                             ((_ is SomeDOMElement) a!23)
                                             (= O B1)
                                             (= (@0DOMElementForm (@0SomeDOMElement a!23))
                                                B1)
                                             (= (ft_emitter K2)
                                                (EmitterForm P O))
                                             (= U1 A1)
                                             (= A1 V)
                                             (= T1 Q)
                                             (= Q W)
                                             (= V W)
                                             (= T (DOMPath nilInt U))
                                             (= P X)
                                             (= X T)
                                             (= X (DOMPath Y (DOMIndex Z)))
                                             (= S1 R)
                                             (= R S)))
                                  (a!33 (= (@0ContentElementScript
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!32)))
                                           N))
                                  (a!34 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!32)))))
                                  (a!35 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!32)))))
                                  (a!45 (= (@0ContentElementScript
                                             (@1DOMElementResource
                                               (@0SomeDOMElement a!44)))
                                           R1))
                                  (a!46 (not ((_ is ContentElementImage)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!44)))))
                                  (a!47 (not ((_ is ContentElementHTML)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!44)))))
                                  (a!61 (ite a!59
                                             (@3ArrayResponse (responses S1))
                                             (ite a!60
                                                  (@4ArrayResponse (responses S1))
                                                  (@defaultArrayResponse
                                                    (responses S1)))))
                                  (a!72 (and (= (blob_origin H2) G2)
                                             (= a!12 (blob_url H2))
                                             (= (url_path a!12)
                                                (url_path_blob G2 F2))
                                             a!71
                                             (= a!66
                                                (SomeContentElement
                                                  (blob_celt H2)))))
                                  (a!81 (and (= (blob_origin C2) B2)
                                             (= a!12 (blob_url C2))
                                             (= (url_path a!12)
                                                (url_path_blob B2 A2))
                                             a!80
                                             (= a!66
                                                (SomeContentElement
                                                  (blob_celt C2)))))
                                  (a!91 (ite ((_ is ProtocolData)
                                               (url_protocol (wd_location U1)))
                                             a!87
                                             a!90))
                                  (a!95 (or ((_ is SSLax) (sc_same_site M2))
                                            ((_ is SSStrict) (sc_same_site M2))
                                            (and (sc_secure M2)
                                                 (= (url_protocol a!12)
                                                    ProtocolHTTPS))))
                                  (a!96 (= (@0domain (@0SomeDomain (sc_domain M2)))
                                           (@0domain (@0SomeDomain (url_host a!12)))))
                                  (a!98 (= (@1subdomain (@0SomeDomain (sc_domain M2)))
                                           (@0domain (@0SomeDomain (url_host a!12)))))
                                  (a!99 (= (@0subdomain (@0SomeDomain (sc_domain M2)))
                                           (@0subdomain (@0SomeDomain (url_host a!12)))))
                                  (a!100 (= (@1subdomain (@0SomeDomain (sc_domain M2)))
                                            (@1subdomain (@0SomeDomain (url_host a!12)))))
                                  (a!106 (and (or (not (sc_secure M2))
                                                  (= (url_protocol a!12)
                                                     ProtocolHTTPS))
                                              (sc_secure M2)
                                              (not ((_ is url_path_blob)
                                                     (url_path a!12)))
                                              (not ((_ is url_path_data)
                                                     (url_path a!12)))
                                              ((_ is SomeDomain)
                                                (url_host a!12))
                                              (= (sc_reg_domain M2)
                                                 (@0SomeDomain (url_host a!12)))
                                              (= (@0url_path_res (url_path a!12))
                                                 slash)
                                              (= (sc_path M2) slash)
                                              (= (sc_domain M2) NoneDomain))))
                            (let ((a!9 (ite (= (ft_correlator K2) 1)
                                            (Build_ArrayoptionprodprodEmitterIntInt
                                              (@0ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              a!5
                                              (@2ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@3ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@4ArrayoptionprodprodEmitterIntInt
                                                (ft_history K2))
                                              (@defaultArrayoptionprodprodEmitterIntInt
                                                (ft_history K2)))
                                            a!8))
                                  (a!36 (and (= A N)
                                             a!33
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!32)))
                                             a!34
                                             a!35
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!32)))
                                             ((_ is SomeDOMElement) a!32)
                                             (= (ft_emitter K2)
                                                (EmitterScript B A))
                                             (= U1 M)
                                             (= T1 C)
                                             (= M H)
                                             (= H I)
                                             (= C I)
                                             (= J F)
                                             (= J (DOMPath K (DOMIndex L)))
                                             (= F (DOMPath nilInt G))
                                             (= B J)
                                             (= S1 D)
                                             (= D E)))
                                  (a!51 (and (= E1 R1)
                                             a!45
                                             ((_ is ContentElementScript)
                                               (@1DOMElementResource
                                                 (@0SomeDOMElement a!44)))
                                             a!46
                                             a!47
                                             (not ((_ is DOMElementForm)
                                                    (@0SomeDOMElement a!44)))
                                             ((_ is SomeDOMElement) a!44)
                                             a!50
                                             (= (ft_emitter K2)
                                                (EmitterCORSPreflight D1 C1))
                                             (= U1 Q1)
                                             (= L1 M1)
                                             (= G1 M1)
                                             (= Q1 L1)
                                             (= T1 G1)
                                             (= J1 (DOMPath nilInt K1))
                                             (= F1 N1)
                                             (= N1 J1)
                                             (= N1 (DOMPath O1 (DOMIndex P1)))
                                             (= S1 H1)
                                             (= H1 I1)))
                                  (a!62 (ite a!57
                                             (@1ArrayResponse (responses S1))
                                             (ite a!58
                                                  (@2ArrayResponse (responses S1))
                                                  a!61)))
                                  (a!73 (or (and (= E2 Q2)
                                                 (= (url_path a!12)
                                                    (url_path_data E2 D2))
                                                 (= a!66 a!69))
                                            a!72))
                                  (a!82 (or (and (= Z1 Q2)
                                                 (= (url_path a!12)
                                                    (url_path_data Z1 Y1))
                                                 (= a!66 a!78))
                                            a!81))
                                  (a!92 (= (SomeOrigin (@0SomeOrigin (rp_hd_access_control_allow_origin
                                                                       a!74)))
                                           (ite a!84 a!85 a!91)))
                                  (a!97 (and a!96
                                             ((_ is domain)
                                               (@0SomeDomain (url_host a!12)))))
                                  (a!101 (ite ((_ is domain)
                                                (@0SomeDomain (url_host a!12)))
                                              a!98
                                              (and a!99 a!100))))
                            (let ((a!10 (ite (= (ft_correlator K2) 0)
                                             (Build_ArrayoptionprodprodEmitterIntInt
                                               a!5
                                               (@1ArrayoptionprodprodEmitterIntInt
                                                 (ft_history K2))
                                               (@2ArrayoptionprodprodEmitterIntInt
                                                 (ft_history K2))
                                               (@3ArrayoptionprodprodEmitterIntInt
                                                 (ft_history K2))
                                               (@4ArrayoptionprodprodEmitterIntInt
                                                 (ft_history K2))
                                               (@defaultArrayoptionprodprodEmitterIntInt
                                                 (ft_history K2)))
                                             a!9))
                                  (a!52 (or (and (= (ft_emitter K2)
                                                    EmitterClient)
                                                 (= U1 T1))
                                            (and (= (ft_emitter K2)
                                                    EmitterWorker)
                                                 (= U1 T1))
                                            a!24
                                            a!36
                                            a!51))
                                  (a!63 (= (ite a!56
                                                (@0ArrayResponse (responses S1))
                                                a!62)
                                           (ite (= J2 0)
                                                (@0ArrayResponse (responses S1))
                                                a!2)))
                                  (a!93 (ite ((_ is EmitterScript)
                                               (ft_emitter K2))
                                             (or (= a!66 NoneContentElement)
                                                 a!92)
                                             (or ((_ is EmitterWorker)
                                                   (ft_emitter K2))
                                                 ((_ is EmitterForm)
                                                   (ft_emitter K2))
                                                 a!92)))
                                  (a!102 (ite ((_ is domain)
                                                (@0SomeDomain (sc_domain M2)))
                                              a!97
                                              a!101)))
                            (let ((a!11 (= W1
                                           (Build_State (+ 1 Q2)
                                                        (Build_FetchEngine
                                                          (+ 1 Q2)
                                                          (ft_emitter K2)
                                                          (ft_request K2)
                                                          (ft_correlator K2)
                                                          a!4
                                                          a!10)
                                                        R2
                                                        T1
                                                        S2
                                                        T2
                                                        U2)))
                                  (a!64 (and (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!53))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!53)))
                                             (= (url_protocol a!12)
                                                ProtocolHTTP)
                                             a!63))
                                  (a!65 (and (or ((_ is ProtocolHTTPS)
                                                   (url_protocol a!53))
                                                 ((_ is ProtocolHTTP)
                                                   (url_protocol a!53)))
                                             (= (url_protocol a!12)
                                                ProtocolHTTPS)
                                             a!63))
                                  (a!94 (or ((_ is EmitterClient)
                                              (ft_emitter K2))
                                            (not ((_ is SomeOrigin)
                                                   (rp_hd_access_control_allow_origin
                                                     a!74)))
                                            a!93))
                                  (a!103 (or (not ((_ is SomeDomain)
                                                    (sc_domain M2)))
                                             a!102)))
                            (let ((a!83 (or a!64
                                            a!65
                                            (and a!73
                                                 (= (rp_hd_access_control_allow_origin
                                                      a!74)
                                                    NoneOrigin)
                                                 (= (rp_hd_location a!74)
                                                    NoneURL)
                                                 (= (url_protocol a!12)
                                                    ProtocolBlob)
                                                 (= a!75 ResponseOk)
                                                 (= (rp_hd_set_cookie a!74)
                                                    NoneSetCookie))
                                            (and a!82
                                                 (= (rp_hd_access_control_allow_origin
                                                      a!74)
                                                    NoneOrigin)
                                                 (= (rp_hd_location a!74)
                                                    NoneURL)
                                                 (= (url_protocol a!12)
                                                    ProtocolData)
                                                 (= a!75 ResponseOk)
                                                 (= (rp_hd_set_cookie a!74)
                                                    NoneSetCookie))))
                                  (a!104 (and (or (not (sc_secure M2))
                                                  (= (url_protocol a!12)
                                                     ProtocolHTTPS))
                                              a!103
                                              ((_ is SomeDomain)
                                                (url_host a!12))
                                              (= (sc_reg_domain M2)
                                                 (@0SomeDomain (url_host a!12)))))
                                  (a!105 (and (or (not (sc_secure M2))
                                                  (= (url_protocol a!12)
                                                     ProtocolHTTPS))
                                              a!103
                                              (sc_secure M2)
                                              ((_ is SomeDomain)
                                                (url_host a!12))
                                              (= (sc_reg_domain M2)
                                                 (@0SomeDomain (url_host a!12))))))
                            (let ((a!107 (ite ((_ is NoPrefix) (sc_name M2))
                                              a!104
                                              (ite ((_ is Secure) (sc_name M2))
                                                   a!105
                                                   a!106))))
                            (let ((a!138 (or (and (= (rp_hd_set_cookie a!74)
                                                     NoneSetCookie)
                                                  (= S2 O2))
                                             (and a!95
                                                  a!107
                                                  (= (rp_hd_set_cookie a!74)
                                                     (SomeSetCookie M2))
                                                  a!109
                                                  a!112
                                                  (= N2 a!137)))))
                            (let ((a!139 (and (Reachable S1 P2 V1)
                                              (= X1 (consEvent a!3 P2))
                                              a!11
                                              (= V1
                                                 (Build_State Q2
                                                              K2
                                                              R2
                                                              T1
                                                              O2
                                                              T2
                                                              U2))
                                              (= a!12 (rq_url (ft_request K2)))
                                              a!15
                                              a!52
                                              a!83
                                              a!94
                                              a!138
                                              ((_ is NoneResponse)
                                                (ft_response K2)))))
                              (=> a!139 (Reachable S1 X1 W1)))))))))))))
                            :weight 0))))
      (a!104 (Build_ArrayoptionprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               (SomeprodprodEmitterIntInt
                 (pairprodEmitterIntInt (pairEmitterInt EmitterClient 540) 0))
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt
               NoneprodprodEmitterIntInt))
      (a!111 (Build_Window 0
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
      (a!120 (asserted (forall ((A Global))
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
(let ((a!6 (Build_ArrayRequest
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 8470)
                                       (url_path_res slash))
                            a!2
                            (SomeInt 11746))
             (Build_Request MethodGet a!3 a!2 (SomeInt 10545))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 11590)
                                       (url_path_data 829 5605))
                            a!2
                            (SomeInt 14106))
             (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 15286)
                                       (url_path_res slash))
                            a!2
                            (SomeInt 8140))
             (Build_Request MethodGet a!4 a!2 (SomeInt 7977))
             (Build_Request MethodGet a!5 a!2 (SomeInt 8116))))
      (a!8 (Build_ResponseHeaders
             (SomeContentType ContentTypeHTML)
             NoneSetCookie
             NoneOrigin
             (SomeURL (Build_URL ProtocolHTTP
                                 NoneDomain
                                 (SomeInt 17241)
                                 (url_path_data 15987 15988)))
             a!7
             NoneReferrerPolicy))
      (a!13 (Build_HTML 4117
                        4118
                        (Build_ArrayoptionHTMLElement
                          a!9
                          NoneHTMLElement
                          a!10
                          (SomeHTMLElement (HTMLScript a!3))
                          a!11
                          a!12)))
      (a!18 (Build_Response (Build_URL ProtocolHTTP
                                       (SomeDomain (subdomain 5437 5438))
                                       (SomeInt 7655)
                                       (url_path_res (anypath 5595)))
                            ResponseOk
                            a!16
                            a!17))
      (a!21 (Build_Response (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 8495)
                                       (url_path_res (anypath 4762)))
                            ResponseOk
                            a!19
                            a!20))
      (a!24 (Build_Response a!3
                            ResponseOk
                            (Build_ResponseHeaders
                              (SomeContentType ContentTypeScript)
                              a!22
                              (SomeOrigin (OpaqueOrigin 14563))
                              NoneURL
                              a!23
                              NoneReferrerPolicy)
                            (SomeContentElement
                              (ContentElementScript (Build_Script a!3 5)))))
      (a!32 (SomeDOMElement (DOMElementResource
                              a!3
                              (ContentElementScript (Build_Script a!3 5)))))
      (a!41 (Build_Document 3786
                            3787
                            (Build_ResponseHeaders
                              NoneContentType
                              NoneSetCookie
                              NoneOrigin
                              NoneURL
                              a!40
                              NoneReferrerPolicy)
                            (Build_HTML 3782
                                        3783
                                        (Build_ArrayoptionHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement
                                          NoneHTMLElement))
                            (Build_DOM 3784
                                       3785
                                       (Build_ArrayoptionDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement))
                            (Build_Initiators (SomeInt 13380)
                                              (Build_ArrayoptionInt
                                                (SomeInt 8270)
                                                (SomeInt 12901)
                                                (SomeInt 6408)
                                                (SomeInt 12846)
                                                (SomeInt 7092)
                                                (SomeInt 7244)))))
      (a!47 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!5
                                                 a!2
                                                 (SomeInt 8116))
                                  1)
                       nilEvent))
      (a!68 (= (rq_url (Build_Request MethodGet a!5 a!2 (SomeInt 8116)))
               (rq_url (Build_Request MethodGet a!3 a!2 (SomeInt 10545)))))
      (a!115 (Build_State 1
                          (Build_FetchEngine
                            1
                            EmitterClient
                            (Build_Request MethodGet a!5 a!2 (SomeInt 8116))
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
                          a!111
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
      (a!117 (Build_Request MethodGet
                            (Build_URL ProtocolHTTP
                                       (SomeDomain (domain 0))
                                       (SomeInt 0)
                                       (url_path_res slash))
                            a!2
                            NoneInt)))
(let ((a!27 (Build_ArrayResponse
              (Build_Response a!5
                              ResponseOk
                              a!8
                              (SomeContentElement (ContentElementHTML a!13)))
              (Build_Response a!4 ResponseOk a!14 a!15)
              a!18
              a!21
              a!24
              (Build_Response (Build_URL ProtocolHTTP
                                         NoneDomain
                                         (SomeInt 9378)
                                         (url_path_data 9666 9667))
                              ResponseOk
                              a!25
                              a!26)))
      (a!35 (Build_Document 6
                            1
                            a!8
                            a!13
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!31)
                                         NoneDOMElement
                                         NoneDOMElement
                                         a!32
                                         (SomeDOMElement a!33)
                                         (SomeDOMElement a!34)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!38 (Build_Document 3
                            1
                            a!8
                            a!13
                            (Build_DOM 1
                                       0
                                       (Build_ArrayoptionDOMElement
                                         (SomeDOMElement a!31)
                                         NoneDOMElement
                                         NoneDOMElement
                                         NoneDOMElement
                                         (SomeDOMElement a!33)
                                         (SomeDOMElement a!34)))
                            (Build_Initiators NoneInt
                                              (Build_ArrayoptionInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt
                                                NoneInt))))
      (a!46 (EvResponse (Build_Response a!5
                                        ResponseOk
                                        a!8
                                        (SomeContentElement
                                          (ContentElementHTML a!13)))
                        1))
      (a!94 (Build_FetchEngine
              5
              EmitterClient
              (Build_Request MethodGet a!3 a!2 (SomeInt 10545))
              2
              (SomeResponse a!24)
              a!90))
      (a!107 (SomeResponse (Build_Response a!5
                                           ResponseOk
                                           a!8
                                           (SomeContentElement
                                             (ContentElementHTML a!13)))))
      (a!118 (Build_State 0
                          (Build_FetchEngine
                            0
                            EmitterClient
                            a!117
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
                          a!111
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
(let ((a!42 (Build_ArrayWindow
              (Build_Window 1 NoneInt a!5 NoneDomain a!35)
              (Build_Window 3767
                            (SomeInt 12246)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 5743)
                                       (url_path_data 11231 11232))
                            NoneDomain
                            a!36)
              (Build_Window 3774
                            (SomeInt 7709)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 7745)
                                       (url_path_data 8950 8951))
                            NoneDomain
                            a!37)
              (Build_Window 1 NoneInt a!5 NoneDomain a!38)
              (Build_Window 3781
                            (SomeInt 10004)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 12684)
                                       (url_path_data 14225 14226))
                            NoneDomain
                            a!39)
              (Build_Window 3788
                            (SomeInt 5671)
                            (Build_URL ProtocolHTTP
                                       NoneDomain
                                       (SomeInt 6503)
                                       (url_path_data 6533 6534))
                            NoneDomain
                            a!41)))
      (a!48 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!3
                                                 a!2
                                                 (SomeInt 10545))
                                  2)
                       (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                  (consEvent a!46 a!47))))
      (a!54 (Build_State 9
                         (Build_FetchEngine
                           9
                           EmitterClient
                           (Build_Request MethodGet a!4 a!2 (SomeInt 7977))
                           3
                           (SomeResponse (Build_Response a!4
                                                         ResponseOk
                                                         a!14
                                                         a!15))
                           a!52)
                         a!53
                         (Build_Window 1 NoneInt a!5 NoneDomain a!35)
                         (Build_ArrayoptionSetCookie
                           a!22
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
      (a!91 (Build_State 8
                         (Build_FetchEngine
                           8
                           EmitterClient
                           (Build_Request MethodGet a!4 a!2 (SomeInt 7977))
                           3
                           NoneResponse
                           a!90)
                         a!53
                         (Build_Window 1 NoneInt a!5 NoneDomain a!35)
                         (Build_ArrayoptionSetCookie
                           a!22
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
      (a!105 (Build_State 4
                          (Build_FetchEngine
                            4
                            EmitterClient
                            (Build_Request MethodGet a!3 a!2 (SomeInt 10545))
                            2
                            NoneResponse
                            a!104)
                          (Build_ServiceWorker
                            0
                            (Build_ArrayoptionInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt
                              NoneInt))
                          (Build_Window 1 NoneInt a!5 NoneDomain a!38)
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
      (a!108 (Build_FetchEngine
               2
               EmitterClient
               (Build_Request MethodGet a!5 a!2 (SomeInt 8116))
               1
               a!107
               a!104)))
(let ((a!45 (Build_Global a!6
                          a!27
                          (Build_ArrayInt 3757 4 3758 3759 3760 0)
                          (Build_ArrayEmitter
                            a!28
                            EmitterClient
                            EmitterClient
                            EmitterClient
                            a!29
                            a!30)
                          a!42
                          a!43
                          (Build_ArrayprodOriginoptionCSP
                            a!44
                            (pairOriginoptionCSP (OpaqueOrigin 10808) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 7656) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 11983) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 6152) NoneCSP)
                            (pairOriginoptionCSP (OpaqueOrigin 10321) NoneCSP))
                          (Build_Config false
                                        false
                                        false
                                        false
                                        true
                                        false
                                        true
                                        false
                                        true
                                        false
                                        false
                                        false)))
      (a!49 (consEvent (EvDOMUpdate (DOMPath nilInt (DOMIndex 3)))
                       (consEvent (EvResponse a!24 2) a!48)))
      (a!55 (ite (= 3 4)
                 (@4ArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54)))
                 (@defaultArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54))))))
(let ((a!50 (consEvent (EvScriptUpdateCache
                         (DOMPath nilInt (DOMIndex 3))
                         4
                         (SomeInt 1))
                       a!49))
      (a!56 (ite (= 3 3)
                 (@3ArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54)))
                 a!55))
      (a!97 (Reachable a!45
                       a!49
                       (Build_State 6
                                    a!94
                                    (Build_ServiceWorker
                                      0
                                      (Build_ArrayoptionInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt
                                        NoneInt))
                                    (Build_Window 1 NoneInt a!5 NoneDomain a!35)
                                    (Build_ArrayoptionSetCookie
                                      a!22
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
      (a!101 (Reachable a!45
                        (consEvent (EvResponse a!24 2) a!48)
                        (Build_State 5
                                     a!94
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
                                                   a!5
                                                   NoneDomain
                                                   a!38)
                                     (Build_ArrayoptionSetCookie
                                       a!22
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
      (a!109 (Reachable a!45
                        (consEvent (EvDOMUpdate (DOMPath nilInt DOMTopLevel))
                                   (consEvent a!46 a!47))
                        (Build_State 3
                                     a!108
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
                                                   a!5
                                                   NoneDomain
                                                   a!38)
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
      (a!112 (Reachable a!45
                        (consEvent a!46 a!47)
                        (Build_State 2
                                     a!108
                                     (Build_ServiceWorker
                                       0
                                       (Build_ArrayoptionInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt
                                         NoneInt))
                                     a!111
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
(let ((a!51 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!4
                                                 a!2
                                                 (SomeInt 7977))
                                  3)
                       a!50))
      (a!57 (ite (= 3 2)
                 (@2ArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54)))
                 a!56)))
(let ((a!58 (ite (= 3 1)
                 (@1ArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54)))
                 a!57))
      (a!92 (=> (Reachable a!45 a!51 a!91)
                (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!95 (=> (Reachable a!45
                           a!50
                           (Build_State 7
                                        a!94
                                        a!53
                                        (Build_Window 1
                                                      NoneInt
                                                      a!5
                                                      NoneDomain
                                                      a!35)
                                        (Build_ArrayoptionSetCookie
                                          a!22
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
                (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!98 (=> a!97
                (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!102 (=> a!101
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!106 (=> (Reachable a!45 a!48 a!105)
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!110 (=> a!109
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!113 (=> a!112
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!116 (=> (Reachable a!45 a!47 a!115)
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))
      (a!119 (=> (Reachable a!45 nilEvent a!118)
                 (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45))))
(let ((a!59 (ite (= 3 0)
                 (@0ArrayoptionprodprodEmitterIntInt
                   (ft_history (st_fetch_engine a!54)))
                 a!58)))
(let ((a!60 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                   (@0SomeprodprodEmitterIntInt a!59)))
               0))
      (a!61 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                   (@0SomeprodprodEmitterIntInt a!59)))
               1))
      (a!62 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                   (@0SomeprodprodEmitterIntInt a!59)))
               2))
      (a!63 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                   (@0SomeprodprodEmitterIntInt a!59)))
               3))
      (a!64 (= (@1pairEmitterInt (@0pairprodEmitterIntInt
                                   (@0SomeprodprodEmitterIntInt a!59)))
               4))
      (a!79 (ite (= (@1pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59))
                    4)
                 (@4ArrayResponse (responses a!45))
                 (@defaultArrayResponse (responses a!45))))
      (a!85 (EvScriptUpdateCache
              (DOMPath nilInt (DOMIndex 3))
              (@1pairEmitterInt (@0pairprodEmitterIntInt
                                  (@0SomeprodprodEmitterIntInt a!59)))
              (SomeInt 1))))
(let ((a!65 (ite a!63
                 (@3ArrayRequest (requests a!45))
                 (ite a!64
                      (@4ArrayRequest (requests a!45))
                      (@defaultArrayRequest (requests a!45)))))
      (a!69 (ite a!63
                 (@3ArrayInt (server_responses a!45))
                 (ite a!64
                      (@4ArrayInt (server_responses a!45))
                      (@defaultArrayInt (server_responses a!45)))))
      (a!80 (ite (= (@1pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59))
                    3)
                 (@3ArrayResponse (responses a!45))
                 a!79))
      (a!86 (consEvent (EvRequest EmitterClient
                                  (Build_Request MethodGet
                                                 a!4
                                                 a!2
                                                 (SomeInt 7977))
                                  3)
                       (consEvent a!85 a!49))))
(let ((a!66 (ite a!61
                 (@1ArrayRequest (requests a!45))
                 (ite a!62 (@2ArrayRequest (requests a!45)) a!65)))
      (a!70 (ite a!61
                 (@1ArrayInt (server_responses a!45))
                 (ite a!62 (@2ArrayInt (server_responses a!45)) a!69)))
      (a!81 (ite (= (@1pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59))
                    2)
                 (@2ArrayResponse (responses a!45))
                 a!80)))
(let ((a!67 (rq_url (ite a!60 (@0ArrayRequest (requests a!45)) a!66)))
      (a!71 (= (ite a!60 (@0ArrayInt (server_responses a!45)) a!70) 0))
      (a!72 (= (ite a!60 (@0ArrayInt (server_responses a!45)) a!70) 1))
      (a!73 (= (ite a!60 (@0ArrayInt (server_responses a!45)) a!70) 2))
      (a!74 (= (ite a!60 (@0ArrayInt (server_responses a!45)) a!70) 3))
      (a!75 (= (ite a!60 (@0ArrayInt (server_responses a!45)) a!70) 4))
      (a!82 (ite (= (@1pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59))
                    1)
                 (@1ArrayResponse (responses a!45))
                 a!81)))
(let ((a!76 (ite a!74
                 (@3ArrayResponse (responses a!45))
                 (ite a!75
                      (@4ArrayResponse (responses a!45))
                      (@defaultArrayResponse (responses a!45)))))
      (a!83 (ite (= (@1pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59))
                    0)
                 (@0ArrayResponse (responses a!45))
                 a!82)))
(let ((a!77 (ite a!72
                 (@1ArrayResponse (responses a!45))
                 (ite a!73 (@2ArrayResponse (responses a!45)) a!76))))
(let ((a!78 (rp_headers (ite a!71 (@0ArrayResponse (responses a!45)) a!77))))
(let ((a!84 (not (= (rp_hd_csp a!78) (rp_hd_csp (rp_headers a!83))))))
(let ((a!87 (and (Reachable a!45 (consEvent (EvWorkerCacheMatch 1) a!51) a!54)
                 ((_ is pairEmitterInt)
                   (@0pairprodEmitterIntInt (@0SomeprodprodEmitterIntInt a!59)))
                 (or ((_ is ProtocolHTTPS) (url_protocol a!67))
                     ((_ is ProtocolHTTP) (url_protocol a!67)))
                 (not (c_worker_allow_synthetic_responses (config a!45)))
                 (not a!68)
                 a!84
                 (= (consEvent (EvWorkerCacheMatch 1) a!51)
                    (consEvent (EvWorkerCacheMatch 1) a!86))
                 ((_ is SomeprodprodEmitterIntInt) a!59)
                 ((_ is pairprodEmitterIntInt)
                   (@0SomeprodprodEmitterIntInt a!59)))))
(let ((a!88 (=> a!87
                (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45))))
(let ((a!99 (hyper-res (hyper-res (hyper-res (hyper-res a!1 a!88) a!89 a!92)
                                  a!93
                                  a!95)
                       a!96
                       a!98)))
(let ((a!114 (hyper-res (hyper-res (hyper-res (hyper-res a!99 a!100 a!102)
                                              a!103
                                              a!106)
                                   a!93
                                   a!110)
                        a!100
                        a!113)))
  (hyper-res (hyper-res (hyper-res a!114 a!103 a!116) a!93 a!119)
             a!120
             (query!0 a!54 (consEvent (EvWorkerCacheMatch 1) a!51) a!45)))))))))))))))))))))))
