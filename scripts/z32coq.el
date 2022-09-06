#!/usr/bin/env -S emacs --script
;; -*- lexical-binding: t  -*-

(require 'cl-lib)
(require 'pcase)
(require 'subr-x)


(defconst event-constructors
  '((EvRequest "Event_request")
    (EvResponse "Event_response")
    (EvDOMUpdate "Event_dom_update")
    (EvScriptUpdateHTML "Event_script_dom_update")
    (EvScriptNavigateFrame "Event_script_navigate_frame")
    (EvScriptPostMessage "Event_script_post_message")
    (EvScriptDomainRelaxation "Event_script_domain_relaxation")
    (EvWorkerCacheMatch "Event_worker_cache_match")
    (EvWorkerUpdateCache "Event_worker_update_cache")
    (EvScriptUpdateCache "Event_script_update_cache")
    (EvScriptSetCookie "Event_script_set_cookie")
    (EvScriptCreateBlobUrl "Event_script_create_blob_url")))


(defun get-string-from-file (filePath)
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))

(defun read-from-stdin ()
  (let ((read nil)
        (contents ""))
    (while (setq read (ignore-errors (read-from-minibuffer "")))
      (setq contents (concat contents "\n" read)))
    contents))

(defun compose (&rest funs)
    (lambda (arg)
      (cl-reduce (lambda (v fn) (funcall fn v))
              (cons arg (reverse funs)))))

(defun eval-list (lst)
  (pcase lst
    (`(cons ,x ,xs) (cons x (eval-list xs)))
    (`nil nil)))


(cl-defun rename-state (state &key (int-start 200))
  (let ((ints (make-hash-table :test #'eql))
        (int-max int-start))
    (cl-labels
        ((replace-bigints (lst)
          (cond ((listp lst) (mapcar #'replace-bigints lst))
                ((and (numberp lst) (>= lst int-start))
                 (let ((hv (gethash lst ints)))
                   (if hv hv (setf (gethash lst ints) (cl-incf int-max)))))
                (t lst)))
         (replace-opts (lst)
          (cond ((listp lst) (mapcar #'replace-opts lst))
                ((and (symbolp lst) (string-prefix-p "Some" (symbol-name lst))) 'Some)
                ((and (symbolp lst) (string-prefix-p "None" (symbol-name lst))) 'None)
                (t lst)))
         (replace-pairs (lst)
          (cond ((listp lst) (mapcar #'replace-pairs lst))
                ((and (symbolp lst) (string-prefix-p "pair" (symbol-name lst))) 'pair)
                (t lst)))
         (replace-lsts (lst)
          (cond ((listp lst) (mapcar #'replace-lsts lst))
                ((and (symbolp lst) (string-prefix-p "cons" (symbol-name lst))) 'cons)
                ((and (symbolp lst) (string-prefix-p "nil" (symbol-name lst))) 'nil)
                (t lst)))
         (replace-arrays (lst)
          (pcase lst
            ((and `(,build? . ,arr)
                  (guard (and (symbolp build?) (string-prefix-p "Build_Array" (symbol-name build?)))))
             (let* ((defval (car (last arr)))
                    (base `(const _ ,(replace-arrays defval)))
                    (idx 0))
               (cl-reduce (lambda (array val)
                            (if (not (equal val defval))
                                (let ((res `(store _ ,array ,idx ,(replace-arrays val))))
                                  (cl-incf idx)
                                  res)
                              (progn (cl-incf idx) array)))
                          (cons base (butlast arr)))))
            ((guard (listp lst)) (mapcar #'replace-arrays lst))
            (_ lst))))
      (funcall (compose
                #'replace-bigints
                #'replace-arrays
                #'replace-lsts
                #'replace-opts
                #'replace-pairs)
               state))))


(defun find-final-state (z3out)
  (cl-labels
      ((expand (env sexp)
               (pcase sexp
                 ((guard (atom sexp)) (let ((envv (assoc sexp env)))
                                           (if envv (cadr envv) sexp)))
                 (_ (mapcar (lambda (x) (expand env x)) sexp))))
       (cons-env (env new-binds)
                 (append (mapcar (pcase-lambda (`(,name ,value))
                                   (list name (expand env value)))
                                 new-binds)
                         env))
       (get-hyp (env sexp)
                (pcase sexp
                  ((guard (atom sexp))
                   (get-hyp env (expand env sexp)))
                  (`(asserted ,@rest) nil)
                  (`(hyper-res ,fst ,snd ,body)
                   (append (get-hyp env fst) (get-hyp env snd) (get-hyp env body)))
                  (`(=> ,hyp ,body)
                   (append (list (expand env hyp)) (get-hyp env body)))
                  (_ nil)))
       (go (env hyp form)
           (pcase form
             (`(let ,binds ,body)
              (go (cons-env env binds) hyp body))
             (`(hyper-res ,fst ,snd ,body)
              (go env (append hyp (get-hyp env fst) (get-hyp env snd)) (expand env body)))
             ((and
               `(,query ,final-state ,lst ,global)
               (guard (string-prefix-p "query!" (symbol-name query))))
              (list :result (expand env final-state) (expand env global) hyp lst))
             (_ nil))))
    (go nil nil z3out)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MAIN

(when (null argv)
  (error "Usage: z32coq.el <infile>"))

(pcase-let ((`(:result ,final-state ,global ,hyps ,evs)
             (rename-state (find-final-state
                            (read (get-string-from-file (car argv)))))))
  (let* ((states (remove nil (mapcar (lambda (x)
                               (pcase x
                                 ((and `(,name ,_ ,_ ,state) (guard (member name '(reachable Reachable)))) state)
                                 (_ nil))) hyps))))
    (sort states
          (pcase-lambda (`(Build_State ,n1 ,@_) `(Build_State ,n2 ,@_))
            (> n1 n2)))
    (let ((sorted-states (reverse states)))
      (mapc #'princ '("Load LoadPath.\n"
                    "From Extractor Require Import Loader.\n"
                    "From Extractor Require Import Array.\n"
                    "Require Import Browser.\n\n"))
      (princ (format "Definition global := %s.\n\n" global))
      (princ (format "Definition events := %s.\n\n" evs))
      (cl-loop for state in sorted-states do
            (princ (format "Definition state_%d := %s.\n\n" (cadr state) state)))
      (princ (format "Definition final_state := %s.\n\n" final-state))

      (princ (format "Definition states := %s.\n"
                     (cl-reduce (lambda (x a) `(cons ,x ,a))
                                (append (mapcar (lambda (s) (format "state_%d" (cadr s))) sorted-states)
                                        (list 'final_state 'nil))
                                :from-end t)))

      (mapc #'princ `("\nLemma final_state_is_reachable: Reachable global events final_state.\n"
                      ,@(mapcar (lambda (ev) (format "  eapply %s.\n" (cadr (assoc (car ev) event-constructors)))) (eval-list evs))
                      "  eapply Initial_state_is_reachable.\n"
                      "  all: repeat try (compute || firstorder || congruence).\n"
                      ;"Qed.\n\n"
                      "Admitted.\n\n"
                      ))

      (mapc #'princ (mapcar (lambda (s) (concat s "\n")) `(
        "Require Extraction."
        "Extraction Language OCaml."
        "Extract Inductive list => \"list\" [ \"[]\" \"(::)\" ]."
        "Extract Inductive prod => \"(*)\"  [ \"(,)\" ]."
        "Extract Inductive unit => \"unit\" [ \"()\" ]."
        "Extract Inductive bool => \"bool\" [ \"true\" \"false\" ]."
        "Extract Inductive option => \"option\" [ \"Some\" \"None\" ]."
        "Extract Inductive nat => int [ \"0\" \"succ\" ] \"(fun fO fS n -> if n=0 then fO () else fS (n-1))\"."
        "Extract Constant plus => \"( + )\"."
        "Extract Constant Nat.eqb => \"( = )\"."
        "Extract Constant Array.array \"'a\" => \"(int * 'a) list\"."
        "Extract Constant Array.const => \"(fun x -> [(-1, x)])\"."
        "Extract Constant Array.store => \"(fun a i x -> (i,x) :: a)\"."
        "Extract Constant Array.select => \"(fun a i -> Option.value (List.assoc_opt i a) ~default:(List.assoc (-1) a))\"."
        "Extract Constant Array.map => \"(fun f a -> List.map (fun (i, x) -> (i, f x)) a)\"."
        ""
        ,(format "Cd \"%s\"." (string-trim (shell-command-to-string "mktemp -d")))
        "Separate Extraction global events states."))))))
