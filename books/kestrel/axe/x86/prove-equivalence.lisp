; Proving equivalence of two x86 binary functions.
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "unroll-x86-code") ; has skip-proofs
(include-book "../tactic-prover")
(include-book "kestrel/strings-light/upcase" :dir :system)

;; todo: add support for extra-rules, extra-proof-rules, and extra-lifting-rules
(defun prove-functions-equivalent-fn (executable1
                                      function1
                                      output1
                                      executable2
                                      function2
                                      output2)
  (declare (xargs :guard (and (stringp executable1)
                              (stringp function1)
                              (output-indicatorp output1)
                              (stringp executable2)
                              (stringp function2)
                              (output-indicatorp output2))))
  (b* (((when (and (equal executable1 executable2)
                   (equal function1 function2)
                   (equal output1 output2)))
        (er hard? 'prove-functions-equivalent-fn "The two functions and executables (and the outputs of interest) are the same."))
       (name1 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable1) "." (acl2::string-upcase-gen function1)))
       (name2 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable1) "." (acl2::string-upcase-gen function2)))
       ((when (eq name1 name2))
        (er hard? 'prove-functions-equivalent-fn "Name clash on ~x0." name1)))
    `(progn
       (def-unrolled ,name1 ,executable1 ; no replacement of register with fresh vars (for now), so that the functions each just take a single param, x86
         :target ,function1
         :output ,output1)
       (def-unrolled ,name2 ,executable2
         :target ,function2
         :output ,output2)
       (prove-equal-with-tactics '(,name1 x86) ; todo: check the arities of the functions (will need to use make-event)
                                 '(,name2 x86)
                                 :tactics '(:rewrite :stp)
                                 ;; todo: support extra rules and default rules:
                                 :rules '(,name1 ,name2)))))

(defmacro prove-functions-equivalent (executable1
                                      function1
                                      output1
                                      executable2
                                      function2
                                      output2)
  (prove-functions-equivalent-fn executable1
                                 function1
                                 output1
                                 executable2
                                 function2
                                 output2))
