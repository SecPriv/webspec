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

Set Primitive Projections.

(* Until there is no support for dune in PG/CoqIDE, we will use this hack. *)
(* https://github.com/ProofGeneral/PG/issues/477 *)
Load LoadPath.
From Extractor Require Import Loader.
From Extractor Require Import Array.
From Extractor Require Import Equality.

Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Bool.Bool.

(******************************************************************************)
(* TYPES                                                                      *)

Definition Index (_: Type) := nat.
Definition Nonce := nat.

(* URL schemes. *)
Variant Protocol :=
| ProtocolHTTP
| ProtocolHTTPS
| ProtocolData
| ProtocolBlob
.

(*
 * Domain names - We avoid the (usual) recursive definition and just distinguish two cases:
 * - a domain represents a registrable domain, which can be bought from a domain registrar;
 * - a subdomain of a registrable domain.
 * These two levels are sufficient to model:
 * - domain relaxation: this feature allows a page to modify the value of the `document.domain` property, which is
 *   used by the browser for SOP checks regarding DOM operations, to an ancestor domain of the original value, up to
 *   the registrable domain. Relaxation is the legacy way to permit communications among windows (frames, popups, etc)
 *   containing same-site documents;
 * - domain cookies: a subdomain can set domain cookies, i.e., cookies that are attached to request to the registrable
 *   domain and all its subdomains.
 *)
Variant Domain :=
| domain (d_dn:nat)
| subdomain (d_ss:nat) (d_sd:nat). (* d:Domain *)

(* Checks whether s is a subdomain of d (where the subdomain relation is reflexive). *)
Definition eq_or_subdomain (s:Domain) (d:Domain) : bool :=
  match s, d with
  | domain sn, domain dn => sn =? dn
  | subdomain sn sdn, subdomain dsn dsdn => sn =? dsn && sdn =? dsdn
  | subdomain sn sdn, domain dn => sdn =? dn
  | domain sn, subdomain dsn dsdn => false
  end.

Definition is_eq_or_subdomain (s:Domain) (d:Domain) : Prop := is_true (eq_or_subdomain s d).

(* Checks whether s and d are same-site domains, i.e., they share the same registrable domain. *)
Definition same_site (s:Domain) (d:Domain) : bool :=
  match s,d with
  | domain sn, domain dn => sn =? dn
  | subdomain _ sn, domain dn => sn =? dn
  | domain sn, subdomain _ dn => sn =? dn
  | subdomain _ sn, subdomain _ dn => sn =? dn
  end.

Definition is_same_site (s:Domain) (d:Domain) : Prop := is_true (same_site s d).

(*
 * Path for URLs and cookies - For now we only consider one level of depth is sufficient to capture
 * the most relevant aspects of path handling for what concerns cookies.
 *)
Variant Path :=
| slash
| anypath (n:nat)
.

(* Checks whether c is a subpath of p (where the subpath relation is reflexive) *)
Definition eq_or_subpath (c:Path) (p:Path) : bool :=
  match c, p with
  | slash, slash         => true
  | anypath _, slash     => true
  | anypath n, anypath m => n =? m
  | _, _                 => false
  end.

Definition is_eq_or_subpath (c:Path) (p:Path) : Prop := is_true (eq_or_subpath c p).


(* We need a specific definition just for the HTTP header `Origin` and CORS headers. *)
(*https://html.spec.whatwg.org/multipage/origin.html#origin*)
Variant Origin :=
| TupleOrigin (origin_protocol: Protocol) (origin_host: option Domain) (origin_port: option nat)
| OpaqueOrigin (origin_nonce: Nonce)
.

(* URLs - Currently we don't model the query string and the fragment; the former would be important
+ * if at some point we need to explicitly model the server behavior or the syntax of scripts embedded
+ * in pages rather than only overapproximating their effect. *)

Variant URLPath :=
| url_path_data (upath_data_nonce: Nonce) (upath_data_idx: nat) (* Index ContentElement *)
| url_path_blob (upath_blob_origin: Origin) (upath_blob_idx: nat)
| url_path_res (upath_res_path: Path)
.

Record URL := {
  url_protocol : Protocol;
  url_host     : option Domain;
  url_port     : option nat;
  url_path     : URLPath;
}.

Definition initial_url : URL :=
  Build_URL ProtocolHTTP (Some (domain 0)) (Some 0) (url_path_res slash).


Definition is_valid_url (u: URL) :=
  match url_protocol u, url_path u with
  | ProtocolHTTP, url_path_res _ | ProtocolHTTPS, url_path_res _ =>
    match url_host u, url_port u with
    | Some _, Some _ => True
    | _, _ => False
    end
  | ProtocolData, url_path_data _ _ =>
    match url_host u, url_port u with
    | None, None => True
    | _, _ => False
    end
  | ProtocolBlob, url_path_blob _ _ =>
    match url_host u, url_port u with
    | None, None => True
    | _, _ => False
    end
  | _, _ => False
  end.

Definition is_local_scheme (u:URL) :=
  match url_protocol u with
  | ProtocolBlob | ProtocolData => True
  | ProtocolHTTPS | ProtocolHTTP => False
  end.

Definition origin_of_url url :=
  match url_protocol url with
  | ProtocolBlob =>
    match url_path url with
    | url_path_blob org _ => Some org
    | _ => None
    end
  | ProtocolData =>
    match url_path url with
    (* https://blog.mozilla.org/security/2017/10/04/treating-data-urls-unique-origins-firefox-57/ *)
    (* https://html.spec.whatwg.org/multipage/origin.html#concept-origin-opaque *)
    | url_path_data nonce _ => Some (OpaqueOrigin nonce)
    | _ => None
    end
  | _ => Some (TupleOrigin (url_protocol url) (url_host url) (url_port url))
  end.

(*
 * Pages can include several type of resources, including scripts, videos, audio files, images and other pages. At the
 * moment we focus on:
 * - scripts: they are a fundamental component for the web ecosystem and are the cause of most security concerns on
 *   the Web
 * - images: they don't have a special semantics in our model, but we want to handle multiple resource types, since
 *   this distinction is relevant when dealing with some policies, e.g., CSP
 * In the future we will support frames.
 *)
Record Image := {
  image_src : URL;
}.

(* We are currently modelling only external scripts. We can easily update the model to support inline script
 * by assigning type `option URL` to `script_src` and letting a `None` URL denote such scripts. *)
Record Script := {
  script_src : URL;
  script_nonce : Nonce;
}.

Variant RequestMethod :=
| MethodGet
| MethodPost
| MethodPut
| MethodDelete
| MethodOptions
.

Record Form := {
  form_method : RequestMethod;
  form_action : URL;
}.


Record Frame := {
  frame_src : URL;
  frame_window : nat; (*Index Window*)
}.

Definition initial_frame := Build_Frame initial_url 0.

(*
 * An `HTMLElement` model nodes in the DOM, which correspond to resources included into the page. Hence, as explained
 * above, we only have images and scripts.
 *)
Variant HTMLElement :=
| HTMLImage (html_image_src : URL)
| HTMLScript (html_script_src : URL)
| HTMLForm (html_form_method : RequestMethod) (html_form_action : URL)
| HTMLFrame (html_frame_src : URL)
.

(* Head component of a page. *)
Definition HTMLHead := nat.
(* We model the body of a page with the list of resources it contains. *)
Definition HTMLBody := array (option HTMLElement).

(* This definition models the content of the body of a HTTP request that fetches an HTML document. *)
Record HTML := {
  html_nonce : Nonce;
  html_head  : HTMLHead;
  html_body  : HTMLBody;
}.

Definition initial_html :=
  Build_HTML 0 0 ([|None|]).

Variant ContentType :=
| ContentTypeHTML
| ContentTypeImage
| ContentTypeScript
.

Variant ContentElement :=
| ContentElementHTML   (celt_html : HTML)
| ContentElementImage  (celt_image : Image)
| ContentElementScript (celt_script : Script)
| ContentElementFrame  (celt_frame : Frame) (celt_frame_html : HTML)
.

Definition content_type_of_element celt : ContentType :=
match celt with
| ContentElementHTML _ => ContentTypeHTML
| ContentElementImage _ => ContentTypeImage
| ContentElementScript _ => ContentTypeScript
| ContentElementFrame _ _ => ContentTypeHTML
end.

Variant DOMElement :=
| DOMElementForm (pg_se_form : Form) (* == DOMElement (StaticElement), StaticElement := Form. *)
| DOMElementResource (pg_sr_src : URL) (pg_sr_ce : ContentElement)
.

Definition DOMHead := nat.
Definition DOMBody := array (option DOMElement).

Record DOM := {
  dm_nonce : Nonce;
  dm_head  : DOMHead;
  dm_body  : DOMBody;
}.

Definition initial_dom :=
  Build_DOM 0 0 ([|None|]).

Variant CookieName :=
| NoPrefix (cn_npn:nat)
| Secure (cn_sn:nat)
| Host (cn_hn:nat)
.

Record CookieMapping := {
  cm_name  : CookieName;
  cm_value : nat;
}.

Variant SameSite :=
| SSStrict
| SSLax
| SSNone
.

Record SetCookie := {
  sc_name       : CookieName;
  sc_value      : nat;
  sc_domain     : option Domain;
  sc_reg_domain : Domain;
  sc_path       : Path;
  sc_secure     : bool;
  sc_http_only  : bool;
  sc_same_site  : SameSite;
}.

Definition Cookie := array (option CookieMapping).

Record RequestHeaders := {
  rq_hd_origin  : option Origin;
  rq_hd_cookie  : Cookie;
  rq_hd_referer : option URL;
}.

Record Request := {
  rq_method  : RequestMethod;
  rq_url     : URL;
  rq_headers : RequestHeaders;
  rq_body    : option nat;
}.

Definition initial_request :=
  Build_Request MethodGet initial_url (Build_RequestHeaders None ([|None|]) None) None.


Variant CSPSrc :=
| CSPSrcNone
| CSPSrcSelf
| CSPSrcScheme (csp_sc_proto: Protocol)
| CSPSrcSource (csp_ss_proto: option Protocol)
               (csp_ss_subdomain: option (option nat))
               (csp_ss_domain:nat)
               (csp_ss_port: option nat)
               (csp_ss_path: option Path)
.

Definition csp_src_match (src: CSPSrc) (self: Origin) (u: URL) : Prop :=
  match src with
  | CSPSrcNone => False
  | CSPSrcSelf => Some self = (origin_of_url u)
  | CSPSrcScheme proto => (url_protocol u) = proto
  | CSPSrcSource proto sub host port path =>
    match proto with
    | None => True
    | Some p => (url_protocol u) = p
    end /\
    match sub, url_host u with
    | None, Some (domain d1) => True
    | Some (None), Some (subdomain s1 d1) => True
    | Some (Some n), Some (subdomain s d1) => s = n
    | _, _ => False
    end /\
    match url_host u with
    | Some (domain d) => d = host
    | Some (subdomain sd1 d) => d = host
    | _ => False
    end /\
    match port with
    | None => True
    | Some prt => (url_port u) = Some prt
    end /\
    match path with
    | None => True
    | Some pth =>
      match url_path u with
      | url_path_res rpth => rpth = pth
      | _ => False
      end
    end
  end.

Record TrustedTypes := {
  tt_policy : option (option nat);
  tt_require_for_script : bool;
}.

Record CSP := {
  csp_script_src : option CSPSrc;
  csp_trusted_types : option TrustedTypes;
}.

Variant ReferrerPolicy :=
| ReferrerPolicyNoReferrer
| ReferrerPolicyOrigin
. (* UnsafeOrigin = None *)

Record ResponseHeaders := {
  rp_hd_content_type                : option ContentType;
  rp_hd_set_cookie                  : option SetCookie;
  rp_hd_access_control_allow_origin : option Origin;
  rp_hd_location                    : option URL;
  rp_hd_csp                         : option CSP;
  rp_hd_referrer_policy             : option ReferrerPolicy;
}.

Definition initial_response_headers :=
  Build_ResponseHeaders None None None None None None.

Variant ResponseCode :=
| ResponseOk (* 200 *)
| ResponseNoContent (* 204 *)
| ResponseFound (* 302 *)
| ResponseTemporaryRedirect (* 307 *)
.

Record Response := {
  rp_url     : URL;
  rp_code    : ResponseCode;
  rp_headers : ResponseHeaders;
  rp_content : option ContentElement;
}.

Definition initial_response :=
  Build_Response initial_url ResponseOk initial_response_headers None.


Variant DOMSelector :=
| DOMTopLevel
| DOMIndex (dm_pt_index : nat)
.

Variant NestedDOMPath :=
| DOMPath (dm_lvs: list nat) (dm_lv_pt: DOMSelector)
.

Variant Emitter :=
| EmitterClient
| EmitterScript (emsc_idx : NestedDOMPath) (emsc_sc : Script)
| EmitterForm (emfm_idx : NestedDOMPath) (emfm_fm : Form)
| EmitterWorker
| EmitterCORSPreflight (emcp_orig_em_idx: nat (*Index Emitter*)) (emcp_orig_rq: Request)
.

Record FetchEngine := {
  ft_version    : nat;
  ft_emitter    : Emitter;
  ft_request    : Request;
  ft_correlator : Nonce;
  ft_response   : option Response;
  ft_history    : array (option (Emitter * Index Request * Index Response));
}.

Definition initial_fetch_engine : FetchEngine :=
  Build_FetchEngine 0 EmitterClient initial_request 0 None ([|None|]).

Record ServiceWorker := {
  wk_version  : nat;
  wk_cache    : array (option (Index Request));
}.

Definition initial_service_worker : ServiceWorker :=
  Build_ServiceWorker 0 ([|None|]).

(*
We model setting `window.location` of a frame as an update of the underlying html of the frame
(see EvScriptNavigateFrame). Doing so we "lose" the initiator of te navigation, so when
we update the html for frame navigation we also store the index of the initiator browsing context
in the Initiators array of the DOM.
*)
Record Initiators := {
  in_toplevel : option nat; (*Index Window*)
  in_body     : array (option nat); (*array (option (Index Window))*)
}.

Definition empty_initiators : Initiators := Build_Initiators None ([|None|]).


Record Document := {
  dc_version : nat;
  dc_nonce   : Nonce;
  dc_headers : ResponseHeaders;
  dc_html    : HTML;
  dc_dom     : DOM;
  dc_init    : Initiators;
}.

Definition initial_document : Document :=
  Build_Document 0 0 initial_response_headers initial_html initial_dom empty_initiators.


(* browsing context: https://www.w3.org/TR/html52/browsers.html#browsing-context *)
Record Window := {
  wd_nonce           : Nonce;
  wd_parent          : option nat; (* Index Window *)
  wd_location        : URL;
  wd_document_domain : option Domain;
  wd_document        : Document;
}.
(* history  : array (option (Index DOM)); WIM has the history of the window; we have a global histoy in the fetch engine *)
(* frames   : array (option (Index Window)); frames = map get_frame (dm_page window.document) *)
(* opener   : option (Index Window); we don't have multiple tabs or windows *)
(* https://www.w3.org/TR/html52/browsers.html#nested-browsing-contexts *)


Definition initial_window := Build_Window 0 None initial_url None initial_document.

Variant Event :=
| EvInit
| EvRequest (evrq_em : Emitter) (evrq_rq : Request) (evrq_corr : Nonce)
| EvResponse (evrp_rp : Response) (evrp_corr : Nonce)
| EvDOMUpdate (evdu_pt : NestedDOMPath)
| EvScriptUpdateHTML (evsdu_sc : NestedDOMPath) (evsdu_pt: NestedDOMPath) (evsdu_ctx: Window)
| EvScriptDomainRelaxation (evsdr_sc : NestedDOMPath) (evsdr_dm: Domain)
| EvWorkerCacheMatch (evwcm_rp : Index Response)
| EvWorkerUpdateCache (ewuc_rq : Index Request) (ewuc_rp : Index Response)
| EvScriptUpdateCache (esuc_pt : NestedDOMPath) (esuc_rq : Index Request)
                      (esuc_rp : option (Index Response))
| EvScriptSetCookie (essc_pt: NestedDOMPath) (essc_ctx: NestedDOMPath)
                    (essc_c_idx: Index SetCookie) (essc_c: SetCookie)
| EvScriptNavigateFrame (esnf_src: NestedDOMPath) (esnf_dst: NestedDOMPath)
                        (snf_frm: Frame) (esnf_loc: URL)
| EvScriptPostMessage (espm_src: NestedDOMPath) (espm_recvr: NestedDOMPath) (espm_dst_orig: option URL)
| EvScriptCreateBlobUrl (escb_pt : NestedDOMPath) (escb_url: URL)
| EvScriptStorageSetItem (esssi_pt : NestedDOMPath) (esssi_og: Origin) (esssi_k: nat) (esssi_v: nat)
.

Definition CookieJar := array (option SetCookie).
Definition initial_cookiejar : CookieJar := [|None|].
Definition cj_http_only := sc_http_only.



Record Blob := {
  blob_url               : URL;
  blob_celt              : ContentElement;
  blob_origin            : Origin;
  blob_csp               : option CSP;
}.

Record StorageItem := {
  si_origin : Origin;
  si_name   : nat;
  si_value  : nat;
}.

Record State := {
  st_version        : nat;
  st_fetch_engine   : FetchEngine;
  st_service_worker : ServiceWorker;
  st_window         : Window;
  st_cookiejar      : array (option SetCookie);
  st_blob_store     : array (option Blob); (* https://w3c.github.io/FileAPI/#BlobURLStore *)
  st_local_storage  : array (option StorageItem);
}.

Definition initial_state : State :=
  Build_State 0 initial_fetch_engine initial_service_worker initial_window ([|None|]) ([|None|]) ([|None|]).

Notation "{{ A , B , C , D , E , F , G }}" := (Build_State A B C D E F G) (at level 80).

Record Config := {
  c_forbidden_headers                      : bool;
  c_restrict_tt_to_secure_contexts         : bool;
  c_tt_strict_realm_check                  : bool;
  c_redirect_preflight_requests            : bool;
  c_origin_header_on_cross_origin_redirect : bool;
  c_earlyhtml5_form_methods                : bool;
  c_script_update_cache                    : bool;
  c_worker_allow_synthetic_responses       : bool;
  c_csp_inherit_local_from_initiator       : bool;
  c_csp_inherit_blob_from_creator          : bool;
  c_domain_relaxation                      : bool;
  c_origin_wide_csp                        : bool;
}.

Record Global := {
  requests         : array Request;
  responses        : array Response;
  server_responses : array (Index Response);
  emitters         : array Emitter; (* untangling of EmitterCORSPreflight *)
  windows          : array Window; (* untangling of Window / ContentElementWindow *)
  data_urls        : array ContentElement;
  origin_csp       : array (Origin * option CSP);
  config           : Config;
}.


(******************************************************************************)
(* PREDICATES                                                                 *)

Definition is_same_origin_request wd rq :=
  (origin_of_url (rq_url rq)) = (origin_of_url (wd_location wd)) /\
  (origin_of_url (rq_url rq)) <> None.

Definition is_cross_origin_request wd rq :=
  not ((origin_of_url (rq_url rq)) = (origin_of_url (wd_location wd))) /\
  (origin_of_url (rq_url rq)) <> None.

Definition is_cors_simple_request rq :=
  (* https://developer.mozilla.org/en-US/docs/Web/HTTP/CORS#simple_requests *)
  (* only GET HEAD POST are allowed *)
  ( (rq_method rq) = MethodGet \/ (rq_method rq) = MethodPost ).

Definition is_wd_initiator_of_idx ctx idx init : Prop :=
  in_body (dc_init (wd_document ctx)).[idx] = init.

Definition is_same_origin_window_domain (w:Window) (c:Window) :=
  (* https://html.spec.whatwg.org/multipage/origin.html#same-origin-domain *)
  match wd_document_domain w, wd_document_domain c with
  | None, None =>
    (origin_of_url (wd_location w)) = (origin_of_url (wd_location c)) /\
    (origin_of_url (wd_location w)) <> None
  | Some wd, Some cd =>
    (url_protocol (wd_location w)) = (url_protocol (wd_location c)) /\ wd = cd
  | _, _ => False
  end.

Definition is_frame_at_page_index pg idx frame fr_html : Prop :=
  match dm_body pg.[idx] with
  | None => False
  | Some (DOMElementForm _) => False
  | Some (DOMElementResource _ elt_rsc) =>
    match elt_rsc with
    | ContentElementHTML _ => False
    | ContentElementImage _ => False
    | ContentElementScript _ => False
    | ContentElementFrame celt_frame celt_frame_html => celt_frame = frame
                                                        /\ celt_frame_html = fr_html
    end
  end.

Definition is_frame_window_at_page_index gb pg idx frame frame_html window :=
  is_frame_at_page_index pg idx frame frame_html /\
  (windows gb).[(frame_window frame)] = window.

Definition is_form_at_page_index pg idx fm : Prop :=
  match dm_body pg.[idx] with
  | None => False
  | Some (DOMElementForm elt_frm) => elt_frm = fm
  | Some (DOMElementResource _ _) => False
  end.

Definition is_allowed_form_method gb mth :=
  match mth with
  | MethodGet | MethodPost => True (* html5 *)
  | MethodPut | MethodDelete => is_true (c_earlyhtml5_form_methods (config gb))
  | _ => False
  end.

Definition is_script_at_page_index pg idx sc : Prop :=
  match dm_body pg.[idx] with
  | None => False
  | Some (DOMElementResource _ elt_rsc) =>
    match elt_rsc with
    | ContentElementHTML _ => False
    | ContentElementImage _ => False
    | ContentElementScript celt_script => celt_script = sc
    | ContentElementFrame celt_frame _ => False (* Use Script_in_dom_path for this *)
    end
  | Some (DOMElementForm _) => False
  end.

Definition is_valid_emitter em gb (wd:Window) : Prop :=
  match em with
  | EmitterClient => True
  | EmitterScript (DOMPath _ (DOMIndex idx)) emsc_sc =>
    is_script_at_page_index (dc_dom (wd_document wd)) idx emsc_sc
  | EmitterScript _ _ => False
  | EmitterForm (DOMPath _ (DOMIndex emfm_idx)) emfm_fm =>
    is_form_at_page_index (dc_dom (wd_document wd)) emfm_idx emfm_fm /\
    is_allowed_form_method gb (form_method emfm_fm)
  | EmitterForm _ _ => False
  | EmitterWorker => True
  | EmitterCORSPreflight emcp_idx emcp_rq =>
    is_cross_origin_request wd emcp_rq /\
    not (is_cors_simple_request emcp_rq)
  end.

(* https://html.spec.whatwg.org/multipage/origin.html#ascii-serialisation-of-an-origin
   If origin is an opaque origin, then return "null". *)
Definition serialize_origin (so: option Origin) : option Origin :=
  match so with
  | Some (OpaqueOrigin _) => None
  | _ => so
  end.

(* https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Referrer-Policy *)
Definition gen_referer (location : URL) (policy : option ReferrerPolicy) : option URL :=
  match policy with
  | None | Some ReferrerPolicyNoReferrer => None
  | Some ReferrerPolicyOrigin =>
    match origin_of_url location with
    | Some (OpaqueOrigin _) => None
    | Some (TupleOrigin proto host port) => Some (Build_URL proto host port (url_path_res slash))
    | _ => None
    end
  end.

(* origin header is added to all requests whose method is neither `GET` nor `HEAD` *)
(* https://fetch.spec.whatwg.org/#origin-header *)
Definition is_valid_emitter_request em rq (wd:Window) ft gb : Prop :=
  (* check preflight request https://fetch.spec.whatwg.org/#cors-preflight-fetch *)
  let check_preflight_request :=
      (is_cross_origin_request wd rq ->
       not (is_cors_simple_request rq) ->
       (* check preflight *)
       match (ft_emitter ft) with
       | EmitterCORSPreflight orig_emitter_idx orig_rq =>
         (* The preflight request was made for this emitter/request *)
         em = ((emitters gb).[orig_emitter_idx]) /\
          rq = orig_rq /\
          (* The response contains the CORS header *)
          match (ft_response ft) with
          | Some preflight_rp =>
            match rp_hd_access_control_allow_origin (rp_headers preflight_rp) with
            | Some allow_ori =>
              (* The allowed origin is the same of the request *)
              match (rq_hd_origin (rq_headers rq)) with
              | Some rq_origin_hd => allow_ori = rq_origin_hd
              | None => False
              end
            | None => False
            end
          | None => False
          end
       | _ => False
       end)
  in
  match em with
  | EmitterClient =>
    rq_method rq = MethodGet /\
    rq_hd_origin (rq_headers rq) = None /\
    rq_hd_referer (rq_headers rq) = None
  | EmitterScript _ emsc_sc =>
    (* Add origin header *)
    rq_hd_origin (rq_headers rq) = serialize_origin (origin_of_url (wd_location wd)) /\
    rq_hd_referer (rq_headers rq) =
    gen_referer (wd_location wd) (rp_hd_referrer_policy (dc_headers (wd_document wd))) /\
    check_preflight_request
  | EmitterForm _ fm =>
    rq_method rq = (form_method fm) /\
    rq_url rq = (form_action fm) /\
    rq_hd_origin (rq_headers rq) = serialize_origin (origin_of_url (wd_location wd)) /\
    rq_hd_referer (rq_headers rq) =
    gen_referer (wd_location wd) (rp_hd_referrer_policy (dc_headers (wd_document wd))) /\
    match (form_method fm) with
    | MethodPut | MethodDelete =>
      (* With method PUT and DELETE we allow only same origin requests (* early html5 *) *)
      is_true (c_earlyhtml5_form_methods (config gb)) /\ is_same_origin_request wd rq
    | _ => True
    end
  | EmitterCORSPreflight emcp_idx emcp_rq =>
    (* The preflight is a cross origin request *)
    is_cross_origin_request wd rq /\
    (* The preflight is a CORS request, so it has a Origin header *)
    rq_hd_origin (rq_headers rq) = serialize_origin (origin_of_url (wd_location wd)) /\
    rq_hd_referer (rq_headers rq) =
    gen_referer (wd_location wd) (rp_hd_referrer_policy (dc_headers (wd_document wd))) /\
    rq_method rq = MethodOptions /\
    rq_url rq = (rq_url emcp_rq)
  | EmitterWorker =>
    rq_hd_origin (rq_headers rq) = serialize_origin (origin_of_url (wd_location wd)) /\
    rq_hd_referer (rq_headers rq) = None /\
    check_preflight_request
  end.

Definition is_valid_fetch_response ft rp corr (wd:Window) : Prop :=
  (ft_response ft) = None
  /\ corr = (ft_correlator ft)
  /\ rp_url rp = rq_url (ft_request ft)
  /\ (* CORS *)
  match rp_hd_access_control_allow_origin (rp_headers rp) with
  | None => True
  | Some ori =>
    match ft_emitter ft with
    | EmitterClient => True
    | EmitterScript _ emsc_sc =>
      Some ori = origin_of_url (wd_location wd) \/ rp_content rp = None
    | EmitterForm _ _ => True
    | EmitterWorker => True
    | EmitterCORSPreflight _ emcp_rq =>
      Some ori = origin_of_url (wd_location wd)
    end
  end.

Definition is_valid_response_content rp : Prop :=
  match rp_hd_content_type (rp_headers rp) with
  | None => True
  | Some cn_tp =>
    match rp_content rp with
    | None => True
    | Some cn_elt =>
      content_type_of_element cn_elt = cn_tp /\
      match cn_elt with
      | ContentElementHTML ct_html => True
      | ContentElementImage ct_image => (image_src ct_image) = rp_url rp
      | ContentElementScript ct_script => (script_src ct_script) = rp_url rp
      | ContentElementFrame ct_frame _ => (frame_src ct_frame) = rp_url rp
      end
    end
  end.

Definition render_static_element opt_htelm :=
  match opt_htelm with
  | None => None
  | Some (HTMLImage _) => None
  | Some (HTMLScript _) => None
  | Some (HTMLFrame _) => None
  | Some (HTMLForm frm_mth frm_act) => Some (DOMElementForm (Build_Form frm_mth frm_act))
  end.

Definition build_toplevel_window vs parent ft rp ct_html :=
  Build_Window (ft_correlator ft) parent (rp_url rp) None
               (Build_Document (S vs) (ft_correlator ft) (rp_headers rp) ct_html
                          (Build_DOM (ft_correlator ft) 0
                                      (map render_static_element (html_body ct_html)))
                          empty_initiators).

Definition update_page_element_at_idx vs wd location dm_pt_idx cn_elt :=
  Build_Window (wd_nonce wd) (wd_parent wd) (wd_location wd) (wd_document_domain wd)
               (Build_Document (S vs) (dc_nonce (wd_document wd))
                          (dc_headers (wd_document wd)) (dc_html (wd_document wd))
                          (Build_DOM
                             (dm_nonce (dc_dom (wd_document wd)))
                             (dm_head (dc_dom (wd_document wd)))
                             (dm_body (dc_dom (wd_document wd)).[dm_pt_idx] <-
                              Some (DOMElementResource location cn_elt)))
                          (dc_init (wd_document wd))).

Definition update_html_element_at_idx vs wd pt_idx html_elt :=
  Build_Window (wd_nonce wd) (wd_parent wd) (wd_location wd) (wd_document_domain wd)
               (Build_Document (S vs) (dc_nonce (wd_document wd))
                          (dc_headers (wd_document wd))
                          (Build_HTML
                                (html_nonce (dc_html (wd_document wd)))
                                (html_head (dc_html (wd_document wd)))
                                (html_body (dc_html (wd_document wd)).[pt_idx] <-
                                 Some html_elt))
                          (Build_DOM
                             (dm_nonce (dc_dom (wd_document wd)))
                             (dm_head  (dc_dom (wd_document wd)))
                             (dm_body  (dc_dom (wd_document wd)).[pt_idx] <-
                              render_static_element (Some html_elt)))
                          (dc_init (wd_document wd))).

Definition update_document_domain (wd:Window) (od: option Domain) :=
  Build_Window (wd_nonce wd) (wd_parent wd) (wd_location wd) od (wd_document wd).

Definition is_valid_content_html_element cn_elt html_elt : Prop :=
  match cn_elt with
  | ContentElementHTML _ => False
  | ContentElementImage celt_image => html_elt = HTMLImage (image_src celt_image)
  | ContentElementScript celt_script => html_elt = HTMLScript (script_src celt_script)
  | ContentElementFrame celt_frame _ => html_elt = HTMLFrame (frame_src celt_frame)
  end.

Definition render_window_dom_path_on_response gb st_vs st_ft rp pt st_wd st_wd_ wd_idx st_bl :=
  match ft_emitter st_ft with
  | EmitterClient => True
  | EmitterForm fm_idx fm_pt => pt = DOMTopLevel
  | EmitterScript sc_idx sc_pt => not (pt = DOMTopLevel) (* a fetch response cannot modify the dom (it can only modify a path, no headers)*)
  | EmitterWorker => False (* worker response needs to be read from cache to be rendered *)
  | EmitterCORSPreflight _ _ => False (* cors preflight is not rendered even if the response is different from 204 *)
  end /\
  ft_response st_ft = Some rp /\

  match rp_code rp with
  | ResponseFound | ResponseTemporaryRedirect =>
    (* 302/307 without location has the same behavior as 200 on firefox and chrome *)
     match (rp_hd_location (rp_headers rp)) with
     | Some url => False
     | None => True
     end
  | ResponseNoContent => False (* no need to navigate away from the current page *)
  | _ => True
  end /\

  is_valid_response_content rp /\
  rp_code rp = ResponseOk /\ (* we don't render redirects *)

  match rp_content rp with
  | None => False
  | Some cn_elt =>
    not (rp_hd_content_type (rp_headers rp) = None) /\
    match pt with
    | DOMTopLevel =>
      match cn_elt with
      | ContentElementImage _ => False
      | ContentElementScript _ => False
      | ContentElementFrame _ _ => False
      | ContentElementHTML ct_html =>
        match url_protocol (rp_url rp) with
        | ProtocolData
        | ProtocolBlob =>
          rp_hd_csp (rp_headers rp) = None
        | _ => True
        end /\
        st_wd_ = build_toplevel_window st_vs None st_ft rp ct_html
      end
    | DOMIndex dm_pt_idx =>
      match html_body (dc_html (wd_document st_wd)).[dm_pt_idx] with
      | None => False
      | Some html_elt =>
        is_valid_content_html_element cn_elt html_elt /\
        match cn_elt with
        | ContentElementFrame ce_fr ce_frhtml =>
          match url_protocol (rp_url rp) with
          | ProtocolData
          | ProtocolBlob => (* Inherit policies when local scheme *)
            let inherit_from_initiator_or_parent :=
                match (in_body (dc_init (wd_document st_wd))).[dm_pt_idx],
                      c_csp_inherit_local_from_initiator (config gb)
                with
                | Some init_idx, true =>
                  (* Inherit from initiator *)
                  rp_hd_csp (rp_headers rp) =
                  rp_hd_csp (dc_headers (wd_document (windows gb.[init_idx])))
                | _, _ =>
                  (* Inherit from parent *)
                  rp_hd_csp (rp_headers rp) =
                  rp_hd_csp (dc_headers (wd_document st_wd_))
                end
            in
            match url_path (rp_url rp) with
            | url_path_blob origin id =>
              match st_bl.[id] with
              | None => False
              | Some blob =>
                if c_csp_inherit_blob_from_creator (config gb) then
                  (* Inherit from creator *)
                  rp_hd_csp (rp_headers rp) = (blob_csp blob)
                else
                  inherit_from_initiator_or_parent
              end
            | _ => inherit_from_initiator_or_parent
            end
          | _ => True (* Do not inherit policies *)
          end /\
          (* Update index of frame is an update_toplevel of inner window *)
          (windows gb).[(frame_window ce_fr)] = build_toplevel_window st_vs (Some wd_idx) st_ft rp ce_frhtml
        | ContentElementScript celt_sc =>
          (* Each rendered script is different *)
          (script_nonce celt_sc) = st_vs /\
          (* Render the script only if it matches the CSP script-src (or there is no CSP)
             that is loaded in the DOM *)
          match rp_hd_csp (dc_headers (wd_document st_wd)) with
          | None => True
          | Some (Build_CSP None _) => True
          | Some (Build_CSP (Some csp_src) _) =>
            match origin_of_url (wd_location st_wd) with
            | Some orign => csp_src_match csp_src orign (script_src celt_sc)
            | None => False
            end
          end
        | _ => True
        end /\
        st_wd_ = update_page_element_at_idx st_vs st_wd (rp_url rp) dm_pt_idx cn_elt
      end
    end
  end.

Definition is_server_response gb rq_idx rp :=
  not (is_local_scheme (rq_url ((requests gb).[rq_idx]))) /\
  (responses gb.[(server_responses gb.[rq_idx])]) = rp.


Definition check_cookie_domain_send (u:URL) (sc:SetCookie) : bool :=
  match sc_domain sc, url_host u with
  | None, Some uh => (* domain attr not set: send only to sc_reg_domain *)
    (sc_reg_domain sc) =? uh
  | Some dattr, Some uh => (* domain attr set: send to all subdomains of dattr *)
    eq_or_subdomain uh dattr
  | _, None => false
  end.

Definition check_cookie_domain_set (u:URL) (sc:SetCookie) : Prop :=
  match url_host u with
  | None => False
  | Some uh =>
    (* store the registering domain *)
    (sc_reg_domain sc) = uh /\
    (* if domain is set, it must be eq to (domain u) or a parent domain *)
    match (sc_domain sc) with
    | None => True
    | Some dattr => (* domain attr set: it can be a parent domain *)
      is_eq_or_subdomain dattr uh
    end
  end.

Definition check_same_site (u:URL) (sc:SetCookie) : Prop :=
  match (sc_same_site sc) with
  (* if a cookie is same-site=none it must have the secure attr *)
  | SSNone => (url_protocol u) = ProtocolHTTPS /\ (sc_secure sc) = true
  | _ => True
  end.

Definition checkb_secure_protocol (u:URL) (sc:SetCookie) : bool :=
  implb (sc_secure sc) (url_protocol u =? ProtocolHTTPS).

Definition check_secure_protocol u sc := is_true (checkb_secure_protocol u sc).


(* SetCookie Constraints *)
Definition is_valid_setcookie (u:URL) (sc:SetCookie) : Prop :=
  check_same_site u sc /\
  match (sc_name sc) with
  | Secure n =>  (* must be set by a secure origin with the secure attribute *)
    (sc_secure sc) = true /\ check_secure_protocol u sc /\
    (* domain must be None or eq or a parent *)
    check_cookie_domain_set u sc
  | Host n =>
    (* must be set by a secure origin with the secure attribute *)
    (sc_secure sc) = true /\ check_secure_protocol u sc
    (* MUST contain a "Path" attribute with a value of "/" *)
    /\ (sc_path sc) = slash /\
    match (url_path u) with
    | url_path_res ru => ru = slash
    | _ => False
    end
    (* domain must be "" *)
    /\ (sc_domain sc) = None
    /\ match url_host u with
       | Some uh => (sc_reg_domain sc) = uh
       | None => False
       end
  | NoPrefix n =>
    (* set with secure mist be https, domain must be None or eq or a parent *)
    check_secure_protocol u sc /\ check_cookie_domain_set u sc
  end.
(* Note: we are not considering the path attribute. It needs to be unconstrained. *)
(* Path attribute does not provide any integrity protection because the
   user agent will accept an arbitrary Path attribute in a Set-Cookie
   header. https://tools.ietf.org/html/rfc6265#section-8.6 *)


(* is True if sc needs to be sent to u *)
(* Note: we are not considering the samesite attribute. see same_site_cookie *)
Definition cookiejar_select_cookie (u:URL) (sc:SetCookie) : bool :=
  check_cookie_domain_send u sc &&
  checkb_secure_protocol u sc &&
  match url_path u with
  | url_path_res ru =>
    eq_or_subpath ru (sc_path sc)
  | _ => false
  end.

Definition same_site_cookie (current_site:Domain) (em:Emitter) (sc:SetCookie) : bool :=
  same_site current_site (sc_reg_domain sc) ||
  match em with
  | EmitterClient => (* toplevel navigation: same-site { lax, None } *)
    (sc_same_site sc) =? SSLax || (sc_same_site sc) =? SSNone
  | EmitterScript _ _ | EmitterWorker => (* script and worker fetch/xhr send cookies *)
    (sc_same_site sc) =? SSNone (* /\ credentials: true *)
  | EmitterForm _ _ => (sc_same_site sc) =? SSNone
  | EmitterCORSPreflight _ _ => false (* Don't send cookies on preflight requests *)
  end.

(* remove cookie from cookie jar *)
(* https://tools.ietf.org/html/rfc6265#section-5.3 (11-12) *)
Definition cookiejar_erase_cookie_mapfn  (name: CookieName) (domain: Domain) (path: Path) (opt_sc: option SetCookie) : option SetCookie :=
  match opt_sc with
  | None => None
  | Some sc =>
    if (sc_name sc) =? name && (sc_reg_domain sc) =? domain && (sc_path sc) =? path
    then None
    else Some sc
  end.

Definition cookiejar_erase_cookie
           (cj: CookieJar) (name: CookieName) (domain: Domain) (path: Path) : CookieJar :=
  map (cookiejar_erase_cookie_mapfn name domain path) cj.

Definition event_request_select_cookie em rq (wd:Window) scopt :=
   match scopt, (url_host (wd_location wd)) with
   | None, _ => None
   | Some sc, Some uh =>
     if cookiejar_select_cookie (rq_url rq) sc
        && same_site_cookie uh em sc
     then Some (Build_CookieMapping (sc_name sc) (sc_value sc))
     else None
   | _, _ => None
   end.


Definition is_redirect gb st corr previous_corr :=
  S previous_corr = corr /\
  match (ft_history (st_fetch_engine st)).[previous_corr] with
  | Some (_, rq_idx, rp_idx) =>
    (rp_code ((responses gb).[rp_idx]) = ResponseFound \/
     rp_code ((responses gb).[rp_idx]) = ResponseTemporaryRedirect) /\
    match (rp_hd_location (rp_headers ((responses gb).[rp_idx]))) with
    | Some url => (rq_url (ft_request (st_fetch_engine st))) = url
    | None => False
    end
  | None => False
  end.

Definition is_cors_authorization_response gb st em_idx (rq: Request) corr rp rp_corr :=
  S rp_corr = corr /\
  match (ft_history (st_fetch_engine st)).[rp_corr] with
  | Some (emitter, rq_idx, rp_idx) =>
    ( emitter = EmitterCORSPreflight em_idx rq) /\
    rp = ((responses gb).[rp_idx]) /\
    match (rp_hd_access_control_allow_origin (rp_headers rp)) with
    | Some origin => True
    | None => False
    end
  | None => False
  end.


Inductive in_redirect_history gb st corr : Nonce -> Prop :=
| History_same : forall corr_p,
    corr = corr_p ->
    in_redirect_history gb st corr corr_p
| History_redirect_base : forall corr_p,
    is_redirect gb st corr corr_p ->
    in_redirect_history gb st corr corr_p
| History_redirect_rec : forall corr_p corr_p_1,
    in_redirect_history gb st corr corr_p_1 ->
    is_redirect gb st corr_p_1 corr_p ->
    in_redirect_history gb st corr corr_p
.


Definition in_history ft corr tuple := (ft_history ft).[corr] = Some tuple.

Definition get_context_csp ctx := rp_hd_csp (dc_headers (wd_document ctx)).
Definition get_response_csp rp := rp_hd_csp (rp_headers rp).

Variant is_request_source (gb: Global) (st: State) (rq: Request) (src: option Origin) : Prop :=
| Req_SRC: forall corr corr_p _hem1 _hem2 _rq_idx _rp_idx rq_idx rp_idx,
  (* rq is the current request *)
  ((ft_request (st_fetch_engine st) = rq /\ ft_correlator (st_fetch_engine st) = corr) \/
  (* rq was sent in a previous state *)
  (ft_history (st_fetch_engine st).[corr] = Some (_hem1, rq_idx, _rp_idx)
   /\ requests gb.[rq_idx] = rq)) /\
  (* was rq in a redirect chain? *)
  in_redirect_history gb st corr corr_p /\
  (if corr =? corr_p then (* no: the src is the origin of the page*)
    src = origin_of_url (wd_location (st_window st))
  else (* yes: the src is the origin of the server that sent the redirection response *)
    ft_history (st_fetch_engine st).[corr_p] = Some (_hem2, _rq_idx, rp_idx) /\
    origin_of_url (rp_url (responses gb.[rp_idx])) = src) ->
  is_request_source gb st rq src.


(******************************************************************************)
(* DOM/Frames Predicates (Recursive Version)                                  *)

(* https://w3c.github.io/webappsec-secure-contexts/ *)
Inductive is_secure_context (gb:Global) : Window -> NestedDOMPath -> Prop :=
| Secure_ctx_base : forall wd pt dompt,
    pt = DOMPath [] dompt ->
    url_protocol (wd_location wd) = ProtocolHTTPS ->
    is_secure_context gb wd pt
| Secure_ctx_rec : forall wd pt frm_idx frm frm_html frm_wd rest_idx dompath,
    pt = DOMPath (frm_idx :: rest_idx) dompath ->
    url_protocol (wd_location wd) = ProtocolHTTPS ->
    is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
    is_secure_context gb frm_wd (DOMPath rest_idx dompath) ->
    is_secure_context gb wd pt
.

Inductive is_not_secure_context (gb:Global) : Window -> NestedDOMPath -> Prop :=
| Not_secure_ctx_base : forall wd pt dompt,
    pt = DOMPath [] dompt ->
    url_protocol (wd_location wd) <> ProtocolHTTPS ->
    is_not_secure_context gb wd pt
| Not_secure_ctx_rec : forall wd pt frm_idx frm frm_html frm_wd rest_idx dompath,
    pt = DOMPath (frm_idx :: rest_idx) dompath ->
    is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
    url_protocol (wd_location wd) <> ProtocolHTTPS \/
    is_not_secure_context gb frm_wd (DOMPath rest_idx dompath) ->
    is_not_secure_context gb wd pt
.


Inductive window_ctx_of_dom_path_rec (gb: Global) (ctx: Window)
  : Window -> NestedDOMPath -> Prop :=
| Window_ctx_pt_base : forall wd pt dompt,
    pt = DOMPath [] dompt ->
    ctx = wd ->
    window_ctx_of_dom_path_rec gb ctx wd pt
| Window_ctx_pt_rec :
    forall wd pt frm_idx frm frm_html frm_wd rest_idx dompath,
      pt = DOMPath (frm_idx :: rest_idx) dompath ->
      is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
      window_ctx_of_dom_path_rec gb ctx frm_wd (DOMPath rest_idx dompath) ->
      window_ctx_of_dom_path_rec gb ctx wd pt.


(* Additional definition to have the parameters in a more reasonable order *)
Variant window_ctx_of_dom_path
        (gb: Global) (wd: Window) (pt: NestedDOMPath) (ctx: Window) : Prop :=
| Window_ctx_in_dom_pt :
    window_ctx_of_dom_path_rec gb ctx wd pt ->
    window_ctx_of_dom_path gb wd pt ctx.


Variant is_script_in_dom_path
        (gb: Global) (wd: Window) (pt: NestedDOMPath) (sc: Script) (ctx: Window) : Prop :=
| Script_in_dom_pt: forall idx lst,
    window_ctx_of_dom_path_rec gb ctx wd pt ->
    pt = DOMPath lst (DOMIndex idx) ->
    is_script_at_page_index (dc_dom (wd_document ctx)) idx sc ->
    is_script_in_dom_path gb wd pt sc ctx
.
(* Note: Inline is needed for BMC assertion error *)


Variant is_form_in_dom_path
        (gb: Global) (wd: Window) (pt: NestedDOMPath) (fm: Form) (ctx: Window) : Prop :=
| Form_in_dom_pt : forall idx lst,
    window_ctx_of_dom_path_rec gb ctx wd pt ->
    pt = DOMPath lst (DOMIndex idx) ->
    is_form_at_page_index (dc_dom (wd_document ctx)) idx fm ->
    is_form_in_dom_path gb wd pt fm ctx
.
(* Note: Inline is needed for BMC assertion error *)


Variant is_frame_in_dom_path
        (gb: Global) (wd: Window) (pt: NestedDOMPath)
        (frm: Frame) (fhtml: HTML) (fwd: Window) (ctx: Window) : Prop :=
| Frame_in_dom_pt: forall idx lst,
    window_ctx_of_dom_path_rec gb ctx wd pt ->
    pt = DOMPath lst (DOMIndex idx) ->
    is_frame_window_at_page_index gb (dc_dom (wd_document ctx)) idx frm fhtml fwd ->
    is_frame_in_dom_path gb wd pt frm fhtml fwd ctx.


Variant is_emitter_window_context gb em wd ctx : Prop :=
| Emitter_window_contex :
  match em with
  | EmitterClient => ctx = wd
  | EmitterScript emsc_idx emsc_sc =>
    is_script_in_dom_path gb wd emsc_idx emsc_sc ctx
  | EmitterForm emfm_idx emfm_fm =>
    is_form_in_dom_path gb wd emfm_idx emfm_fm ctx
  | EmitterWorker => ctx = wd
  | EmitterCORSPreflight orig_emitter_idx emcp_rq =>
    match ((emitters gb).[orig_emitter_idx]) with
    | EmitterScript emsc_idx emsc_sc =>
      is_script_in_dom_path gb wd emsc_idx emsc_sc ctx
    | _ => False
    end
  end ->
  is_emitter_window_context gb em wd ctx
.


Inductive update_window_on_response (gb:Global) (vs:nat) (ft:FetchEngine)
                                    (bl: array (option Blob)) (rp:Response)
  : NestedDOMPath -> Window -> Window -> Prop :=

| Render_window_base : forall pt wd wd_ lz_pt wd_idx,
    pt = DOMPath [] lz_pt ->
    (windows gb).[wd_idx] = wd_ ->
    render_window_dom_path_on_response gb vs ft rp lz_pt wd wd_ wd_idx bl ->
    update_window_on_response gb vs ft bl rp pt wd wd_

| Render_window_rec :
    forall pt wd wd_ frm_idx frm frm_html frm_wd frm_wd_ rest_idx dompath frm_wd_idx_,
    pt = DOMPath (frm_idx :: rest_idx) dompath ->
    is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
    update_window_on_response gb vs ft bl rp (DOMPath rest_idx dompath) frm_wd frm_wd_ ->
    (windows gb).[frm_wd_idx_] = frm_wd_ ->
    wd_ = update_page_element_at_idx
            vs wd (rp_url rp) frm_idx
            (ContentElementFrame (Build_Frame (frame_src frm) frm_wd_idx_) frm_html) ->
    update_window_on_response gb vs ft bl rp pt wd wd_
.


Inductive update_window_html_from_ctx (gb:Global) (vs:nat) (ctx:Window) (elt: HTMLElement)
  : NestedDOMPath -> Window -> Window -> Prop :=

| Update_html_base : forall pt wd wd_ pt_idx,
    pt = DOMPath [] (DOMIndex pt_idx) ->
    is_same_origin_window_domain wd ctx ->
    wd_ = update_html_element_at_idx vs wd pt_idx elt ->
    update_window_html_from_ctx gb vs ctx elt pt wd wd_

| Update_html_rec :
    forall pt wd wd_ frm_idx frm frm_html frm_wd frm_wd_ rest_idx dompath frm_wd_idx_,
    pt = DOMPath (frm_idx :: rest_idx) dompath ->
    is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
    update_window_html_from_ctx gb vs ctx elt (DOMPath rest_idx dompath) frm_wd frm_wd_ ->
    (windows gb).[frm_wd_idx_] = frm_wd_ ->
    wd_ =  update_page_element_at_idx vs wd (wd_location frm_wd) frm_idx
                    (ContentElementFrame (Build_Frame (frame_src frm) frm_wd_idx_)
                                         (dc_html (wd_document frm_wd_))) ->
    update_window_html_from_ctx gb vs ctx elt pt wd wd_
.


Inductive update_window_domain_from_ctx (gb:Global) (vs:nat) (ctx:Window) (maybedm: option Domain)
  : NestedDOMPath -> Window -> Window -> Prop :=

| Update_domain_base : forall pt wd wd_ lz_pt,
    pt = DOMPath [] lz_pt ->
    wd_ = update_document_domain wd maybedm ->
    update_window_domain_from_ctx gb vs ctx maybedm pt wd wd_

| Update_domain_rec :
    forall pt wd wd_ frm_idx frm frm_html frm_wd frm_wd_ rest_idx dompath frm_wd_idx_,
    pt = DOMPath (frm_idx :: rest_idx) dompath ->
    is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
    update_window_domain_from_ctx gb vs ctx maybedm (DOMPath rest_idx dompath) frm_wd frm_wd_ ->
    (windows gb).[frm_wd_idx_] = frm_wd_ ->
    wd_ = update_page_element_at_idx vs wd (wd_location frm_wd) frm_idx
               (ContentElementFrame (Build_Frame (frame_src frm) frm_wd_idx_) frm_html) ->
    update_window_domain_from_ctx gb vs ctx maybedm pt wd wd_
.

Definition update_initiator_at_idx wd elm_idx (init_idx: option nat) : Window :=
  Build_Window (wd_nonce wd) (wd_parent wd) (wd_location wd) (wd_document_domain wd)
               (Build_Document
                  (dc_version (wd_document wd))
                  (dc_nonce (wd_document wd))
                  (dc_headers (wd_document wd))
                  (dc_html (wd_document wd))
                  (dc_dom (wd_document wd))
                  (Build_Initiators (in_toplevel (dc_init (wd_document wd)))
                                    ((in_body (dc_init (wd_document wd))).[elm_idx] <-
                                     init_idx))).

Inductive update_html_req_initiator (gb: Global) (vs:nat) (init_idx: option nat) : NestedDOMPath -> Window -> Window -> Prop :=
| Update_init_base : forall pt wd wd_ pt_idx,
    pt = DOMPath [] (DOMIndex pt_idx) ->
    wd_ = update_initiator_at_idx wd pt_idx init_idx ->
    update_html_req_initiator gb vs init_idx pt wd wd_
| Upate_init_rec :
    forall pt wd wd_ frm_idx frm frm_html frm_wd frm_wd_ rest_idx dompath frm_wd_idx_,
      pt = DOMPath (frm_idx :: rest_idx) dompath ->
      is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
      update_html_req_initiator gb vs init_idx (DOMPath rest_idx dompath) frm_wd frm_wd_ ->
      (windows gb).[frm_wd_idx_] = frm_wd_ ->
      wd_ = update_page_element_at_idx vs wd (wd_location frm_wd) frm_idx
              (ContentElementFrame (Build_Frame (frame_src frm) frm_wd_idx_) frm_html) ->
      update_html_req_initiator gb vs init_idx pt wd wd_
.

Inductive is_valid_setcookie_from_ctx (gb:Global) (vs:nat) (ctx:Window) (setcookie: SetCookie) :
                                       Window -> NestedDOMPath -> Prop :=
| Valid_setcookie_base : forall wd pt,
    pt = DOMPath [] DOMTopLevel ->
    is_same_origin_window_domain ctx wd ->
    is_valid_setcookie (wd_location wd) setcookie ->
    is_valid_setcookie_from_ctx gb vs ctx setcookie wd pt

| Valid_setcookie_rec :
    forall wd pt frm_idx frm frm_html frm_wd rest_idx dompath,
      pt = DOMPath (frm_idx :: rest_idx) dompath ->
      is_frame_window_at_page_index gb (dc_dom (wd_document wd)) frm_idx frm frm_html frm_wd ->
      is_valid_setcookie_from_ctx gb vs ctx setcookie frm_wd (DOMPath rest_idx dompath) ->
      is_valid_setcookie_from_ctx gb vs ctx setcookie wd pt
.


(******************************************************************************)
(* Script Knowledge                                                           *)


Variant ScriptObject :=
| SOUrl (so_url: URL)
| SOHTML (so_htelt: HTMLElement)
| SOTrustedHTML (so_trusted_realm: Window) (so_trusted_htelt: HTMLElement)
| SODOMElt (so_dmelt: DOMElement)
| SOCookie (so_sc_idx: Index SetCookie) (so_cm: CookieMapping)
| SOSetCookie (so_sc: SetCookie)
| SORequestHeaders (so_rqh: RequestHeaders)
| SORequest (so_rq: Request)
| SOResponseHeaders (so_rph: ResponseHeaders)
| SOResponse (so_rp: Response)
| SODOMRef (so_dm_pt: NestedDOMPath)
| SOStorageItem (so_si: StorageItem)
.

Definition remove_forbidden_rp_headers gb rphd :=
  (* https://fetch.spec.whatwg.org/#forbidden-response-header-name *)
  if c_forbidden_headers (config gb) then
    Build_ResponseHeaders
      (rp_hd_content_type rphd)
      None (* Remove cookies *)
      (rp_hd_access_control_allow_origin rphd)
      (rp_hd_location rphd)
      (rp_hd_csp rphd)
      (rp_hd_referrer_policy rphd)
  else rphd.

Inductive Scriptstate (gb: Global) (st: State) (sc: Script) : ScriptObject -> Prop :=
| Script_destructure_rp_url : forall (rp: Response),
    Scriptstate gb st sc (SOResponse rp) ->
    Scriptstate gb st sc (SOUrl (rp_url rp))

| Script_destructure_rp_hd : forall (rp: Response),
    Scriptstate gb st sc (SOResponse rp) ->
    Scriptstate gb st sc (SOResponseHeaders
                            (remove_forbidden_rp_headers gb (rp_headers rp)))

| Script_destructure_rp_hd_cookie : forall (rp: Response) rphd c_,
    Scriptstate gb st sc (SOResponseHeaders rphd) ->
    match (rp_hd_set_cookie rphd) with
    | None => False
    | Some c => c = c_
    end ->
    Scriptstate gb st sc (SOSetCookie c_)

| Script_destructure_rp_hd_cookie_mapping : forall (rp: Response) c c_idx,
    Scriptstate gb st sc (SOSetCookie c) ->
    (st_cookiejar st).[c_idx] = Some c ->
    Scriptstate gb st sc (SOCookie c_idx (Build_CookieMapping (sc_name c) (sc_value c)))

| Script_read_document_cookie : forall (pt: NestedDOMPath) (wd_ctx:Window) (c_idx: Index SetCookie) cookie_,
    is_script_in_dom_path gb (st_window st) pt sc wd_ctx ->
    match (st_cookiejar st).[c_idx] with
    | None => False
    | Some cookie =>
      is_true (cookiejar_select_cookie (wd_location wd_ctx) cookie) /\
      (sc_http_only cookie) = false /\
      cookie_ = cookie
    end ->
    Scriptstate gb st sc (SOCookie c_idx (Build_CookieMapping (sc_name cookie_) (sc_value cookie_)))

| Script_read_fetch_response : forall (pt: NestedDOMPath) (wd_ctx:Window) (rp: Response),
    is_script_in_dom_path gb (st_window st) pt sc wd_ctx ->
    (ft_emitter (st_fetch_engine st)) = EmitterScript pt sc ->
    (ft_response (st_fetch_engine st)) = Some rp ->
    Scriptstate gb st sc (SOResponse rp)

| Script_construct_trusted_type : forall (pt: NestedDOMPath) (wd_ctx:Window) (elt: HTMLElement),
    is_script_in_dom_path gb (st_window st) pt sc wd_ctx ->
    match rp_hd_csp (dc_headers (wd_document wd_ctx)) with
    | Some (Build_CSP _ (Some (Build_TrustedTypes tt_policy _))) =>
      match tt_policy with
      | None => (* The script can always create trusted types *) True
      | Some (None) => (* `trusted-types;` the script cannot create them *) False
      | Some (Some policy) => (* `trusted-types policy;` the script can w/ policy *) True
      end
    | None | Some (Build_CSP _ None) => (* No header, the script can create TTs *) True
    end ->
    Scriptstate gb st sc (SOTrustedHTML wd_ctx elt)

| Script_read_dom :
    forall (pt: NestedDOMPath) (wd_ctx:Window) (target: NestedDOMPath) (target_ctx: Window),
    is_script_in_dom_path gb (st_window st) pt sc wd_ctx ->
    window_ctx_of_dom_path gb (st_window st) target target_ctx ->
    is_same_origin_window_domain wd_ctx target_ctx ->
    Scriptstate gb st sc (SODOMRef target)
| Script_get_storage_item:
    forall (pt: NestedDOMPath) (wd_ctx:Window) (s_idx: Index StorageItem) storage_item org,
      is_script_in_dom_path gb (st_window st) pt sc wd_ctx ->
      match (st_local_storage st).[s_idx] with
      | None => False
      | Some si =>
        origin_of_url (wd_location wd_ctx) = Some org /\
        (si_origin si) = org /\ storage_item = si
      end ->
      Scriptstate gb st sc (SOStorageItem storage_item)
.


(******************************************************************************)
(* REACHABLE                                                                  *)


Inductive Reachable (gb: Global) : list Event -> State -> Prop :=
| Initial_state_is_reachable :
    distinct (requests gb) ->
    distinct (responses gb) ->
    distinct (map fst (origin_csp gb)) ->
    (* origin_csp gb.[0] = (TupleOrigin ProtocolHTTP (Some (domain 0)) (Some 0), None, None) -> *)
    match origin_of_url initial_url with
    | Some initial_origin => origin_csp gb.[0] = (initial_origin, None)
    | _ => False
    end ->
    Reachable gb [] (initial_state)

| Event_request :
  forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_ft_ wd_ctx,
  forall (em: Emitter) (rq: Request) (corr: Nonce),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    corr = S (ft_correlator st_ft) ->
    is_emitter_window_context gb em st_wd wd_ctx ->
    is_valid_emitter em gb wd_ctx ->
    is_valid_url (rq_url rq) ->

    (* Follow redirect if the last response is a redirect *)
    (* Otherwise continue normally *)
    match (ft_response st_ft) with
    | Some rp =>
      let handle_preflight_requests :=
          if c_redirect_preflight_requests (config gb) then True
          else match em with
               | EmitterCORSPreflight _ _ => False
               | _ => True
               end in
      let set_origin_header_on_redirect :=
          if c_origin_header_on_cross_origin_redirect (config gb) then
            (* preserve origin on redirect *)
            rq_hd_origin (rq_headers rq) = (rq_hd_origin (rq_headers (ft_request st_ft)))
          else (* Preserve origin header only if same origin *)
            if origin_of_url (rq_url rq) =? origin_of_url (rq_url (ft_request st_ft)) then
              rq_hd_origin (rq_headers rq) = (rq_hd_origin (rq_headers (ft_request st_ft)))
            else rq_hd_origin (rq_headers rq) = None in
      let set_referer_header_on_redirect :=
          rq_hd_referer (rq_headers rq) = None in
      match (rp_code rp) with
      | ResponseFound => (* 302 *)
        handle_preflight_requests /\
        match (rp_hd_location (rp_headers rp)) with
        | Some url =>
          rq_url rq = url /\ (* follow redirect *)
          ft_emitter st_ft = em /\ (* follow with the same emitter type *)
          set_origin_header_on_redirect /\
          set_referer_header_on_redirect /\
          (rq_method rq) = MethodGet /\ (* force a GET request *)
          (rq_body rq) = None (* strip request body *)
        | None => is_valid_emitter_request em rq wd_ctx st_ft gb (* check origin header only if it is not a redirect *)
        end
      | ResponseTemporaryRedirect =>
        handle_preflight_requests /\
         match (rp_hd_location (rp_headers rp)) with
         | Some url =>
           rq_url rq = url /\ (* follow redirect *)
           ft_emitter st_ft = em /\ (* follow with the same emitter type *)
           set_origin_header_on_redirect /\
           set_referer_header_on_redirect /\
           (rq_method rq) = (rq_method (ft_request st_ft)) /\ (* preserve method *)
           (rq_body rq) = (rq_body (ft_request st_ft)) (* preserve body *)
         | None =>  is_valid_emitter_request em rq wd_ctx st_ft gb (* check origin header only if it is not a redirect *)
         end
      | _ => is_valid_emitter_request em rq wd_ctx st_ft gb (* check origin header only if it is not a redirect *)
      end
    | _ => is_valid_emitter_request em rq wd_ctx st_ft gb (* check origin header only if it is not a redirect *)
    end ->

    match url_protocol (rq_url rq) with
    | ProtocolData =>
      rq_hd_cookie (rq_headers rq) = ([| None |]) /\ em = EmitterClient
    | ProtocolBlob =>
      rq_hd_cookie (rq_headers rq) = ([| None |]) /\ em = EmitterClient /\
      match url_path (rq_url rq) with
      | url_path_blob origin id =>
        match st_bl.[id] with
        | None => False
        | Some blob => rq_url rq = (blob_url blob) /\ blob_origin blob = origin
        end
      | _ => False
      end
    | _ =>
      (* Set Cookie header *)
      rq_hd_cookie (rq_headers rq) = map (event_request_select_cookie em rq wd_ctx) st_cj
    end ->
    st_ft_ = Build_FetchEngine (S st_vs) em rq corr None (ft_history st_ft) ->

    Reachable gb (EvRequest em rq corr :: st_ev) ({{ S st_vs, st_ft_, st_wk, st_wd, st_cj, st_bl, st_sg }})


| Event_response :
  forall st_vs st_ev st_ft st_wk st_wd (st_cj : CookieJar) st_sg  st_ft_ st_cj_e (st_cj_ : CookieJar) c_idx st_bl wd_ctx,
  forall (rq_idx: Index Request) (rp_idx: Index Response),
  forall (rp: Response) (corr: Nonce),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    rp = (responses gb.[rp_idx]) ->
    ft_request st_ft = (requests gb.[rq_idx]) ->

    is_emitter_window_context gb (ft_emitter st_ft) st_wd wd_ctx ->

    is_valid_fetch_response st_ft rp corr wd_ctx ->

    match url_protocol (rp_url rp) with
    | ProtocolData
    | ProtocolBlob =>
      rp_code rp = ResponseOk /\
      rp_hd_access_control_allow_origin (rp_headers rp) = None /\
      rp_hd_location (rp_headers rp) = None /\
      rp_hd_set_cookie (rp_headers rp) = None /\
      match url_path (rp_url rp) with
      | url_path_data nonce celt_idx =>
        rp_content rp = Some (data_urls gb.[celt_idx]) /\
        nonce = st_vs
      | url_path_blob origin id =>
        match st_bl.[id] with
        | None => False
        | Some blob =>
          rp_url rp = (blob_url blob) /\ blob_origin blob = origin /\
          rp_content rp = Some (blob_celt blob)
        end
      | _ => False
      end
    | _ => is_server_response gb rq_idx rp (* is_server_response applies to network messages *)
    end ->

    st_ft_ = Build_FetchEngine (S st_vs)
               (ft_emitter st_ft) (ft_request st_ft) (ft_correlator st_ft)
               (Some rp)
               (ft_history st_ft.[corr] <- Some (ft_emitter st_ft, rq_idx, rp_idx)) ->

    (* add setCookie to cookiejar *)
    match (rp_hd_set_cookie (rp_headers rp)) with
    | None => st_cj_ = st_cj
    | Some setcookie =>
      (* add constraints on setCookie fields name, domain, path, secure *)
      is_valid_setcookie (rp_url rp) setcookie /\
      (* erase exisitng cookies with the same name,domain and insert the new one *)
      st_cj_e = cookiejar_erase_cookie st_cj (sc_name setcookie) (sc_reg_domain setcookie) (sc_path setcookie) /\
      st_cj_e.[c_idx] = None /\
      st_cj_ = (st_cj_e.[c_idx] <- Some setcookie)
    end ->

    Reachable gb (EvResponse rp corr :: st_ev) ({{ S st_vs, st_ft_, st_wk, st_wd, st_cj_, st_bl, st_sg }})


| Event_dom_update :
 forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_wd_ st_bl_ origin_idx,
 forall (rp: Response) (pt: NestedDOMPath),
   Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

   (* Set the origin-wide CSP if the configuration option is enabled *)
   (if c_origin_wide_csp (config gb)
    then
      match origin_csp gb.[origin_idx], origin_of_url (rp_url rp) with
      | (orig, csp), Some url_orig =>
        orig = url_orig /\ rp_hd_csp (rp_headers rp) = csp
      | _, _ => False
      end
    else True) ->

   update_window_on_response gb st_vs st_ft st_bl rp pt st_wd st_wd_ ->

   match pt with
   | DOMPath _ (DOMTopLevel) => st_bl_ = [| None |]
   | _ => st_bl_ = st_bl
   end ->

   Reachable gb (EvDOMUpdate pt :: st_ev) ({{ S st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl_, st_sg }})

| Event_script_dom_update :
  forall st st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_wd_ sc wd_ctx target_ctx st_wd_2 realm,
  forall (sc_pt: NestedDOMPath) (target_pt: NestedDOMPath) (elt: HTMLElement),
    Reachable gb st_ev st ->
    st = ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    is_script_in_dom_path gb st_wd sc_pt sc wd_ctx ->
    window_ctx_of_dom_path gb st_wd target_pt target_ctx ->

    (* Check trusted types enforcement *)
    match rp_hd_csp (dc_headers (wd_document target_ctx)) with
    | Some (Build_CSP _ (Some (Build_TrustedTypes _ true))) =>
      (* Restrict to secure contexts
         (chrome 83, fixed in chrome 84 (may 2020), but mar 8 2021 in the spec) *)
      if c_restrict_tt_to_secure_contexts (config gb) then
        (
          (is_secure_context gb st_wd target_pt /\
           Scriptstate gb st sc (SOTrustedHTML realm elt) )
        \/
          (is_not_secure_context gb st_wd target_pt /\
           True)
        )
      else
        Scriptstate gb st sc (SOTrustedHTML realm elt)
    | _ => (* No header, the script can use the sink *) True
    end ->
    (if c_tt_strict_realm_check (config gb) then
       realm = target_ctx
     else True)
    ->
    update_window_html_from_ctx gb st_vs wd_ctx elt target_pt st_wd st_wd_ ->
    (* here we assume target_pt is not DOMPathTopLevel *)
    update_html_req_initiator gb st_vs None target_pt st_wd_ st_wd_2 -> (* always inherit from parent *)


    Reachable gb (EvScriptUpdateHTML sc_pt target_pt target_ctx :: st_ev)
              ({{ S st_vs, st_ft, st_wk, st_wd_2, st_cj, st_bl, st_sg }})

| Event_script_navigate_frame :
    forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_wd_ sc wd_ctx st_wd_2
           target_ctx target_level target_idx target_fr target_html ninit_idx,
    forall (sc_pt: NestedDOMPath) (pt: NestedDOMPath) (loc: URL),
      Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->
      is_script_in_dom_path gb st_wd sc_pt sc wd_ctx ->
      (* https://seclab.stanford.edu/websec/frames/navigation/ *)
      (* Descendant policy *)
      (*window_ctx_of_dom_path gb wd_ctx pt target_ctx ->*)
      window_ctx_of_dom_path gb st_wd pt target_ctx ->
      pt = DOMPath target_level (DOMIndex target_idx) ->
      is_frame_at_page_index (dc_dom (wd_document target_ctx)) target_idx target_fr target_html ->
      update_window_html_from_ctx gb st_vs target_ctx (HTMLFrame loc) pt st_wd st_wd_ ->
      (* Inherit policies from wd_ctx (the navigator initiator) *)
      (windows gb).[ninit_idx] = wd_ctx ->
      update_html_req_initiator gb st_vs (Some ninit_idx) pt st_wd_ st_wd_2 ->

      Reachable gb (EvScriptNavigateFrame sc_pt pt target_fr loc :: st_ev)
                ({{ S st_vs, st_ft, st_wk, st_wd_2, st_cj, st_bl, st_sg }})

| Event_script_post_message :
    forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg sc wd_ctx sc_dst dst_ctx,
    forall (sc_pt: NestedDOMPath) (sc_recvr: NestedDOMPath) (dst_orig: option URL),
      Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->
      is_script_in_dom_path gb st_wd sc_pt sc wd_ctx ->
      is_script_in_dom_path gb st_wd sc_recvr sc_dst dst_ctx ->
      (* Check origin dst *)
      match dst_orig with
      | None => True
      | Some orig_url => (origin_of_url orig_url) = (origin_of_url (wd_location dst_ctx))
      end ->
      Reachable
        gb (EvScriptPostMessage sc_pt sc_recvr dst_orig :: st_ev) ({{ S st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }})

| Event_script_domain_relaxation :
  forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_wd_ sc wd_ctx,
  forall (sc_pt: NestedDOMPath) (dmn: Domain),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    is_true (c_domain_relaxation (config gb)) ->
    is_script_in_dom_path gb st_wd sc_pt sc wd_ctx ->
    (* https://developer.mozilla.org/en-US/docs/Web/API/Document/domain#setter *)
    (*  A script can set the value of document.domain to its current
        domain or a superdomain of its current domain. *)
    match (url_host (wd_location wd_ctx)) with
    | Some uh =>
      is_eq_or_subdomain uh dmn
    | None => False
    end ->

    update_window_domain_from_ctx gb st_vs wd_ctx (Some dmn) sc_pt st_wd st_wd_ ->

    Reachable gb (EvScriptDomainRelaxation sc_pt dmn :: st_ev) ({{ S st_vs, st_ft, st_wk, st_wd_, st_cj, st_bl, st_sg }})


| Event_worker_cache_match :
  forall st_vs st_ev st_ft st_wk st_dm st_cj st_bl st_sg st_ft_,
  forall (rq_idx: Index Request) (rp_idx: Index Response),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg }}) ->

    not (ft_emitter st_ft = EmitterWorker) ->
    not (is_local_scheme (rq_url (ft_request st_ft))) ->
    ft_request st_ft = (requests gb.[rq_idx]) ->
    ft_response st_ft = None ->
    (wk_cache st_wk).[rq_idx] = Some rp_idx ->
    (* set the cached response correlator as the current one *)
    is_valid_fetch_response st_ft (responses gb.[rp_idx]) (ft_correlator st_ft) st_dm ->
    st_ft_ = Build_FetchEngine (S st_vs)
               (ft_emitter st_ft) (ft_request st_ft) (ft_correlator st_ft)
               (Some (responses gb.[rp_idx]))
               (ft_history st_ft.[(ft_correlator st_ft)] <-
                Some (ft_emitter st_ft, rq_idx, rp_idx)) ->

    Reachable gb (EvWorkerCacheMatch rp_idx :: st_ev) ({{ S st_vs, st_ft_, st_wk, st_dm, st_cj, st_bl, st_sg }})


| Event_worker_update_cache :
  forall st_vs st_ev st_ft st_wk st_dm st_cj st_bl st_sg st_wk_,
  forall (rq_idx: Index Request) (rp_idx: Index Response),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_dm, st_cj, st_bl, st_sg }}) ->
    (
      if c_worker_allow_synthetic_responses (config gb) then
        not (is_local_scheme (rp_url (responses gb.[rp_idx])))
      else
        not (is_local_scheme (rq_url (ft_request st_ft))) /\
        ft_request st_ft = (requests gb.[rq_idx]) /\
        ft_response st_ft = Some (responses gb.[rp_idx])
    ) ->
    st_wk_ = Build_ServiceWorker (S st_vs)
               ((wk_cache st_wk).[rq_idx] <- Some rp_idx) ->

    Reachable gb (EvWorkerUpdateCache rq_idx rp_idx :: st_ev) ({{ S st_vs, st_ft, st_wk_, st_dm, st_cj, st_bl, st_sg }})


| Event_script_update_cache :
  forall st_vs st_ev st_ft st_wk st_wd st_bl st_cj st_sg st_wk_ rp wd_ctx,
  forall (pt: NestedDOMPath) (sc: Script)
         (rq_idx: Index Request) (rp_idx_opt: option (Index Response)),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    is_true (c_script_update_cache (config gb)) ->
    not (is_local_scheme (rp_url rp)) ->
    match rp_idx_opt with
    | Some rp_idx => (responses gb).[rp_idx] = rp
                  /\ (rq_url ((requests gb).[rq_idx])) = (rp_url rp)
    | _ => True
    end ->
    is_script_in_dom_path gb st_wd pt sc wd_ctx ->
    is_same_origin_request wd_ctx ((requests gb).[rq_idx]) ->
    st_wk_ = Build_ServiceWorker (S st_vs) ((wk_cache st_wk).[rq_idx] <- rp_idx_opt) ->

    Reachable gb (EvScriptUpdateCache pt rq_idx rp_idx_opt :: st_ev) ({{ S st_vs, st_ft, st_wk_, st_wd, st_cj, st_bl, st_sg }})


| Event_script_set_cookie :
  forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_cj_e st_cj_ wd_ctx,
  forall (pt: NestedDOMPath) (sc: Script) (wd_set: NestedDOMPath)
         (c_idx: Index SetCookie) (setcookie: SetCookie),
    Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

    is_script_in_dom_path gb st_wd pt sc wd_ctx ->

    (* set-cookie constraints depend on the window in which the script sets document.cookie *)
    is_valid_setcookie_from_ctx gb st_vs wd_ctx setcookie st_wd wd_set ->

    (* set-cookie js constraints: cannot set httponly *)
    (sc_http_only setcookie) = false ->
    st_cj_e = cookiejar_erase_cookie st_cj (sc_name setcookie)
                                     (sc_reg_domain setcookie) (sc_path setcookie) /\
    st_cj_e.[c_idx] = None /\
    st_cj_ = (st_cj_e.[c_idx] <- Some setcookie) ->

    Reachable
      gb (EvScriptSetCookie pt wd_set c_idx setcookie :: st_ev) ({{ S st_vs, st_ft, st_wk, st_wd, st_cj_, st_bl, st_sg }})

| Event_script_create_blob_url :
    forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_bl_ wd_ctx,
    forall (pt: NestedDOMPath) (sc: Script) (u: URL) (blob: Blob) (blob_idx: nat),
      Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

      is_script_in_dom_path gb st_wd pt sc wd_ctx ->

      (blob_url blob) = u ->
      Some (blob_origin blob) = (origin_of_url (wd_location wd_ctx)) ->
      (if c_csp_inherit_blob_from_creator (config gb) then
        (blob_csp blob) = (rp_hd_csp (dc_headers (wd_document wd_ctx)))
      else True) ->
      is_valid_url u ->
      match url_path u with
      | url_path_blob org idx => org = (blob_origin blob) /\ idx = blob_idx
      | _ => False
      end ->
      st_bl.[blob_idx] = None ->
      st_bl_ = (st_bl.[blob_idx] <- Some blob) ->
      Reachable gb (EvScriptCreateBlobUrl pt u :: st_ev) ({{ S st_vs, st_ft, st_wk, st_wd, st_cj, st_bl_, st_sg }})

| Event_script_storage_set_item :
    forall st_vs st_ev st_ft st_wk st_wd st_cj st_bl st_sg st_sg_ st_sg_tmp,
    forall wd_ctx pt sc st_idx storage_item org,
      Reachable gb st_ev ({{ st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg }}) ->

      is_script_in_dom_path gb st_wd pt sc wd_ctx ->

      origin_of_url (wd_location wd_ctx) = Some org ->
      si_origin storage_item = org ->
      st_sg_tmp = map (fun (opt_si: option StorageItem) =>
                         match opt_si with
                         | None => None
                         | Some si =>
                           if (si_origin si) =? org && (si_name si) =? (si_name storage_item)
                           then None
                           else Some si
                         end) st_sg ->
      st_sg_ = (st_sg_tmp.[st_idx] <- Some storage_item) ->

      Reachable gb (EvScriptStorageSetItem pt org (si_name storage_item) (si_value storage_item) :: st_ev)
                ({{ S st_vs, st_ft, st_wk, st_wd, st_cj, st_bl, st_sg_ }})
.
