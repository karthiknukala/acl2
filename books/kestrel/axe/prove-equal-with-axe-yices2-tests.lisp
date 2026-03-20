; Tests of prove-equal-with-axe using the Yices2 backend
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-yices2)

(include-book "std/testing/must-fail" :dir :system)
(include-book "equivalence-checker")
(include-book "rules1")
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; A likely constant top node, proved through the Yices2 pure-node path.
(deftest
  (prove-equal-with-axe '(equal (bvxor '8 x x) 0)
                        ''t
                        :backend :yices2
                        :yices2-timeout-secs 10
                        :initial-rule-sets nil
                        :types :bytes
                        :max-conflicts nil))

;; A pure equality case that uses the equivalence-checker SMT backend.
(deftest
  (prove-equal-with-axe (dagify-term! '(bvplus '8 '7 x))
                        (dagify-term! '(bvplus '8 x '7))
                        :backend :yices2
                        :yices2-timeout-secs 10
                        :initial-rule-sets nil
                        :types :bytes
                        :max-conflicts nil))

(must-fail
  (prove-equal-with-axe (dagify-term! '(bvplus '8 '7 x))
                        (dagify-term! '(bvmult '8 x '7))
                        :backend :yices2
                        :yices2-timeout-secs 10
                        :initial-rule-sets nil
                        :types :bytes))
