; Utilities for testing prove-with-yices2
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prove-with-yices2" :ttags :all)

(defun must-prove-with-yices2-fn (name term counterexamplep timeout-secs print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null timeout-secs)
                                  (natp timeout-secs)))
                  :mode :program
                  :stobjs state))
  (mv-let (result state)
    (translate-and-prove-term-with-yices2 term counterexamplep nil timeout-secs print (symbol-name name) state)
    (if (eq *error* result)
        (prog2$ (er hard? 'must-prove-with-yices2 "Error ~x0 running test." name)
                (mv (erp-t) :error state))
      (if (not (eq *valid* result))
          (prog2$ (er hard? 'must-prove-with-yices2 "Test ~x0 was supposed to prove." name)
                  (mv (erp-t) :fail state))
        (prog2$ (cw "TEST ~x0 PASSED.~%" name)
                (mv (erp-nil) '(progn) state))))))

(defmacro must-prove-with-yices2 (name term
                                       &key
                                       (counterexample 't)
                                       (timeout-secs '*default-yices2-timeout-secs*)
                                       (print 'nil))
  `(make-event (must-prove-with-yices2-fn ',name ,term ',counterexample ,timeout-secs ',print state)))

(defun must-not-prove-with-yices2-fn (name term counterexamplep timeout-secs print state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null timeout-secs)
                                  (natp timeout-secs)))))
  (mv-let (result state)
    (translate-and-prove-term-with-yices2 term counterexamplep nil timeout-secs print (symbol-name name) state)
    (if (eq *error* result)
        (prog2$ (er hard? 'must-not-prove-with-yices2 "Error running test ~x0." name)
                (mv (erp-t) :error state))
      (if (eq *valid* result)
          (prog2$ (er hard? 'must-not-prove-with-yices2 "Test ~x0 was supposed to fail." name)
                  (mv (erp-t) :fail state))
        (prog2$ (cw "TEST ~x0 PASSED" name)
                (mv (erp-nil) '(progn) state))))))

(defmacro must-not-prove-with-yices2 (name term
                                           &key
                                           (counterexample 't)
                                           (timeout-secs '*default-yices2-timeout-secs*)
                                           (print 'nil))
  `(make-event (must-not-prove-with-yices2-fn ',name ,term ',counterexample ,timeout-secs ',print state)))
