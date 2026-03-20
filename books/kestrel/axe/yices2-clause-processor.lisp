; A clause-processor that calls Yices2
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book requires a :ttag (translate-dag-to-smtlib2) because of the call to define-trusted-clause-processor.

(include-book "prove-with-yices2")

(set-verify-guards-eagerness 0)

(defund yices2-clause-processor (clause hint state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (symbol-alistp hint))
                  :stobjs state))
  (b* ((hint-keys (strip-cars hint))
       (allowed-hint-keys '(:counterexample :timeout-secs :must-prove :print))
       ((when (not (subsetp-equal hint-keys allowed-hint-keys)))
        (er hard? 'yices2-clause-processor "Unsupported keys in hint: ~x0." (set-difference-equal hint-keys allowed-hint-keys))
        (mv :bad-hint (list clause) state))
       (counterexample (lookup-eq :counterexample hint))
       ((when (not (booleanp counterexample)))
        (er hard? 'yices2-clause-processor "Bad :counterexample option, ~x0, in hint ~x1." counterexample hint)
        (mv :bad-hint (list clause) state))
       (timeout-pair (assoc-eq :timeout-secs hint))
       ((when (and timeout-pair
                   (not (natp (cdr timeout-pair)))))
        (er hard? 'yices2-clause-processor "Bad :timeout-secs option, ~x0, in hint ~x1." (cdr timeout-pair) hint)
        (mv :bad-hint (list clause) state))
       (timeout-secs (if timeout-pair (cdr timeout-pair) *default-yices2-timeout-secs*))
       (must-prove (lookup-eq :must-prove hint))
       ((when (not (booleanp must-prove)))
        (er hard? 'yices2-clause-processor "Bad :must-prove option, ~x0, in hint ~x1." must-prove hint)
        (mv :bad-hint (list clause) state))
       (print (lookup-eq :print hint))
       ((when (not (print-levelp print)))
        (er hard? 'yices2-clause-processor "Bad :print option, ~x0, in hint ~x1." print hint)
        (mv :bad-hint (list clause) state))
       ((mv result state)
        (prove-clause-with-yices2 clause
                                  counterexample
                                  nil
                                  timeout-secs
                                  print
                                  "YICES2-CLAUSE-PROC"
                                  state)))
    (if (eq *error* result)
        (mv (erp-t) (list clause) state)
      (if (eq *valid* result)
          (mv (erp-nil) nil state)
        (if must-prove
            (prog2$ (er hard? 'yices2-clause-processor "Failed to prove but :must-prove was given.")
                    (mv (erp-t) (list clause) state))
          (mv (erp-nil) (list clause) state))))))

(define-trusted-clause-processor
  yices2-clause-processor
  nil
  :ttag translate-dag-to-smtlib2)

(defund defthm-with-yices2-clause-processor-fn (name term must-prove timeout-secs counterexample print rule-classes)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp must-prove)
                              (or (null timeout-secs)
                                  (symbolp timeout-secs)
                                  (natp timeout-secs))
                              (booleanp counterexample)
                              (print-levelp print))))
  `(defthm ,name ,term
     :hints (("Goal" :clause-processor (yices2-clause-processor clause
                                                                (list (cons :must-prove ',must-prove)
                                                                      (cons :timeout-secs ,timeout-secs)
                                                                      (cons :counterexample ',counterexample)
                                                                      (cons :print ',print))
                                                                state)))
     ,@(if (eq :auto rule-classes) nil `(:rule-classes ,rule-classes))))

(defmacro defthm-with-yices2-clause-processor (name
                                                    term
                                                    &key
                                                    (rule-classes ':auto)
                                                    (timeout-secs '*default-yices2-timeout-secs*)
                                                    (counterexample 't)
                                                    (must-prove 't)
                                                    (print ':brief))
  (defthm-with-yices2-clause-processor-fn name term must-prove timeout-secs counterexample print rule-classes))

(set-verify-guards-eagerness 2)
