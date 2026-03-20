; Tests of the Yices2 clause processor
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-yices2)

; Matt K. mod: Avoid ACL2(p) with waterfall-parallelism, "Clause-processors
; that return one or more stobjs are not officially supported when waterfall
; parallelism is enabled."
(set-waterfall-parallelism nil)

(include-book "yices2-clause-processor")
(include-book "std/testing/must-fail" :dir :system)

(defthm yices2-clause-processor-test-0
  (not (not (equal (bvplus 32 x y)
                   (bvplus 32 y x))))
  :hints (("Goal" :in-theory nil
           :clause-processor (yices2-clause-processor clause nil state))))

(defthm yices2-clause-processor-test-0b
  (not (not (equal (bvplus 32 x y)
                   (bvplus 32 y x))))
  :hints (("Goal" :in-theory nil
           :clause-processor yices2-clause-processor)))

(must-fail
  (defthm yices2-clause-processor-fail-1
    (not (not (equal (bvplus 32 x y)
                     (bvplus 32 x z))))
    :hints (("Goal" :in-theory nil
             :clause-processor (yices2-clause-processor clause nil state)))))

(defthm yices2-clause-processor-test-1
  (not (not (equal (bvplus 32 x y)
                   (bvplus 32 y x))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil
           :clause-processor (yices2-clause-processor clause '((:print . t)) state))))

(defthm yices2-clause-processor-test-2
  (not (not (equal (bvplus 32 x y)
                   (bvplus 32 y x))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil
           :clause-processor (yices2-clause-processor clause '((:timeout-secs . 5)) state))))

(defthm-with-yices2-clause-processor defthm-with-yices2-clause-processor-test-1
  (equal (bvplus 32 x y)
         (bvplus 32 y x)))

(defthm-with-yices2-clause-processor defthm-with-yices2-clause-processor-test-2
  (equal (bvplus 32 x y)
         (bvplus 32 x y))
  :rule-classes nil)
