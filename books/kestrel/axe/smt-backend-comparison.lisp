; Utilities for comparing the STP and Yices2 SMT backends on the same terms
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/get-real-time" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)

(include-book "prove-with-stp" :ttags :all)
(include-book "prove-with-yices2" :ttags :all)

(defun smt-backend-result-kind (result)
  (declare (xargs :guard t))
  (cond ((eq result *valid*) :valid)
        ((eq result *invalid*) :invalid)
        ((eq result *timedout*) :timedout)
        ((eq result *error*) :error)
        ((and (consp result)
              (eq (car result) *counterexample*))
         :invalid)
        ((and (consp result)
              (eq (car result) *possible-counterexample*))
         :invalid)
        (t :unexpected)))

(defun smt-backend-returned-counterexamplep (result)
  (declare (xargs :guard t))
  (and (consp result)
       (or (eq (car result) *counterexample*)
           (eq (car result) *possible-counterexample*))))

(defun faster-smt-backend (stp-seconds yices2-seconds)
  (declare (xargs :guard (and (rationalp stp-seconds)
                              (rationalp yices2-seconds))))
  (cond ((< stp-seconds yices2-seconds) :stp)
        ((< yices2-seconds stp-seconds) :yices2)
        (t :tie)))

(defun run-term-with-stp-and-time (name term counterexamplep max-conflicts print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :mode :program
                  :stobjs state))
  (mv-let (start-real-time state)
    (get-real-time state)
    (mv-let (result state)
      (translate-and-prove-term-with-stp term
                                         counterexamplep
                                         nil
                                         max-conflicts
                                         print
                                         (concatenate 'string
                                                      "smt-backend-comparison-"
                                                      (symbol-name name)
                                                      "-stp")
                                         state)
      (mv-let (elapsed state)
        (real-time-since start-real-time state)
        (mv result elapsed state)))))

(defun run-term-with-yices2-and-time (name term counterexamplep timeout-secs print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null timeout-secs)
                                  (natp timeout-secs)))
                  :mode :program
                  :stobjs state))
  (mv-let (start-real-time state)
    (get-real-time state)
    (mv-let (result state)
      (translate-and-prove-term-with-yices2 term
                                            counterexamplep
                                            nil
                                            timeout-secs
                                            print
                                            (concatenate 'string
                                                         "smt-backend-comparison-"
                                                         (symbol-name name)
                                                         "-yices2")
                                            state)
      (mv-let (elapsed state)
        (real-time-since start-real-time state)
        (mv result elapsed state)))))

(defun compare-smt-backends-fn (name term counterexamplep stp-max-conflicts yices2-timeout-secs print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null stp-max-conflicts)
                                  (natp stp-max-conflicts))
                              (or (null yices2-timeout-secs)
                                  (natp yices2-timeout-secs)))
                  :mode :program
                  :stobjs state))
  (mv-let (stp-result stp-seconds state)
    (run-term-with-stp-and-time name term counterexamplep stp-max-conflicts print state)
    (mv-let (yices2-result yices2-seconds state)
      (run-term-with-yices2-and-time name term counterexamplep yices2-timeout-secs print state)
      (let* ((stp-counterexamplep (smt-backend-returned-counterexamplep stp-result))
             (yices2-counterexamplep (smt-backend-returned-counterexamplep yices2-result))
             (stp-kind (smt-backend-result-kind stp-result))
             (yices2-kind (smt-backend-result-kind yices2-result))
             (faster (faster-smt-backend stp-seconds yices2-seconds)))
        (cond
         ((or (eq stp-kind :unexpected)
              (eq yices2-kind :unexpected))
          (prog2$ (er hard? 'compare-smt-backends-fn
                      "Unexpected backend result for ~x0.  STP returned ~X12 and Yices2 returned ~X34."
                      name stp-result nil yices2-result nil)
                  (mv (erp-t) :unexpected state)))
         ((or (eq stp-kind :error)
              (eq yices2-kind :error))
          (prog2$ (er hard? 'compare-smt-backends-fn
                      "Backend error for ~x0.  STP returned ~X12 and Yices2 returned ~X34."
                      name stp-result nil yices2-result nil)
                  (mv (erp-t) :error state)))
         ((or (eq stp-kind :timedout)
              (eq yices2-kind :timedout))
          (prog2$ (er hard? 'compare-smt-backends-fn
                      "Backend timeout for ~x0.  STP returned ~X12 and Yices2 returned ~X34."
                      name stp-result nil yices2-result nil)
                  (mv (erp-t) :timedout state)))
         ((not (eq stp-kind yices2-kind))
          (prog2$ (er hard? 'compare-smt-backends-fn
                      "Backends disagreed on ~x0.  STP returned ~X12 and Yices2 returned ~X34."
                      name stp-result nil yices2-result nil)
                  (mv (erp-t) :disagreement state)))
         ((and counterexamplep
               (eq stp-kind :invalid)
               (not (equal stp-counterexamplep yices2-counterexamplep)))
          (prog2$ (er hard? 'compare-smt-backends-fn
                      "Backends disagreed on counterexample availability for ~x0.  STP returned ~X12 and Yices2 returned ~X34."
                      name stp-result nil yices2-result nil)
                  (mv (erp-t) :counterexample-disagreement state)))
         (t
          (prog2$
           (cw "COMPARE ~x0 PASSED: kind=~x1, STP=~x2s, Yices2=~x3s, faster=~x4.~%"
               name stp-kind stp-seconds yices2-seconds faster)
           (mv (erp-nil) '(progn) state))))))))

(defmacro compare-smt-backends (name term
                                     &key
                                     (counterexample 'nil)
                                     (stp-max-conflicts '*default-stp-max-conflicts*)
                                     (yices2-timeout-secs '*default-yices2-timeout-secs*)
                                     (print 'nil))
  `(make-event (compare-smt-backends-fn ',name
                                        ,term
                                        ',counterexample
                                        ,stp-max-conflicts
                                        ,yices2-timeout-secs
                                        ',print
                                        state)))
