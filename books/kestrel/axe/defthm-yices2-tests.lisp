; Tests of defthm-yices2
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-yices2)

(include-book "defthm-yices2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defthm-yices2 test1
    (equal (bvplus 32 x y)
           (bvplus 32 y x))))

(must-fail
  (defthm-yices2 test2
    (equal (bvplus 32 x y)
           (bvplus 32 x z))))

(deftest
  (defthm-yices2 test3
    (equal (bvplus 32 x y)
           (bvplus 32 x y))
    :rule-classes nil))

(must-fail
  (defthm-yices2 test4
    (equal (bvplus 32 x y)
           (bvplus 32 x z))
    :counterexample t))

(deftest
  (defthm-yices2 array-commute
    (equal (bv-array-write 8 100 7 val1
                           (bv-array-write 8 100 4 val2 data))
           (bv-array-write 8 100 4 val2
                           (bv-array-write 8 100 7 val1 data)))))
