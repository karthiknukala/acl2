; A tool for proving an ACL2 theorem using Yices2.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prove-with-yices2")

(defun defthm-yices2-fn (name term rule-classes counterexamplep timeout-secs print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null timeout-secs)
                                  (natp timeout-secs))
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (b* (((mv result state)
        (translate-and-prove-term-with-yices2 term counterexamplep
                                              nil
                                              timeout-secs
                                              print
                                              (symbol-name name)
                                              state)))
    (if (eq result *valid*)
        (mv nil
            `(skip-proofs
               (defthm ,name
                 ,term
                 :rule-classes ,rule-classes))
            state)
      (prog2$ (er hard? 'defthm-yices2 "Failed to prove the theorem ~x0.  Result was ~X12." name result nil)
              (mv t nil state)))))

(defmacro defthm-yices2 (name
                              term
                              &key
                              (rule-classes '(:rewrite))
                              (timeout-secs '*default-yices2-timeout-secs*)
                              (counterexample 'nil)
                              (print 'nil))
  `(make-event (defthm-yices2-fn ',name ',term ',rule-classes ',counterexample ,timeout-secs ',print state)))
