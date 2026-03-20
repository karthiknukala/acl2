; Tests of prove-with-yices2
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-yices2)

(include-book "prove-with-yices2-tester" :ttags :all)
(include-book "translate-dag-to-smtlib2")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (parse-yices2-output-objects '(UNSAT) nil)
              *valid*)

(assert-equal (parse-yices2-output-objects '(UNKNOWN) nil)
              *timedout*)

(assert-equal (parse-yices2-output-objects '(SAT) nil)
              *invalid*)

(assert-equal (parse-yices2-output-objects '(SAT) t)
              *error*)

(assert-equal (car (parse-yices2-output-objects '(SAT ((NODE0 #b00000101)
                                                       (NODE1 TRUE)
                                                       ((SELECT NODE2 #b00) #b00010001)
                                                       ((SELECT NODE2 #b01) #b00010010)))
                                                t))
              *counterexample*)

(assert-equal (cdr (assoc-equal 0
                                (cadr (parse-yices2-output-objects '(SAT ((NODE0 #b00000101)
                                                                          (NODE1 TRUE)
                                                                          ((SELECT NODE2 #b00) #b00010001)
                                                                          ((SELECT NODE2 #b01) #b00010010)))
                                                                   t))))
              5)

(assert-equal (cdr (assoc-equal 1
                                (cadr (parse-yices2-output-objects '(SAT ((NODE0 #b00000101)
                                                                          (NODE1 TRUE)
                                                                          ((SELECT NODE2 #b00) #b00010001)
                                                                          ((SELECT NODE2 #b01) #b00010010)))
                                                                   t))))
              t)

(assert-equal (cdr (assoc-equal '(2 . 0)
                                (cadr (parse-yices2-output-objects '(SAT ((NODE0 #b00000101)
                                                                          (NODE1 TRUE)
                                                                          ((SELECT NODE2 #b00) #b00010001)
                                                                          ((SELECT NODE2 #b01) #b00010010)))
                                                                   t))))
              17)

(assert-equal (cdr (assoc-equal '(2 . 1)
                                (cadr (parse-yices2-output-objects '(SAT ((NODE0 #b00000101)
                                                                          (NODE1 TRUE)
                                                                          ((SELECT NODE2 #b00) #b00010001)
                                                                          ((SELECT NODE2 #b01) #b00010010)))
                                                                   t))))
              18)

(must-prove-with-yices2 commutative-bvxor
                        '(equal (bvxor 32 x y)
                                (bvxor 32 y x)))

(must-not-prove-with-yices2 non-commutative-bvxor
                            '(equal (bvxor 32 x y)
                                    (bvxor 32 x x))
                            :counterexample t)

(must-prove-with-yices2 bvsx-32-16-def
                        '(implies (unsigned-byte-p 64 x)
                                  (equal (bvsx 32 16 x)
                                         (bvif 32
                                               (equal 1 (getbit 15 x))
                                               (bvcat 16 65535 16 (bvsx 32 16 x))
                                               (bvsx 32 16 x)))))

(must-prove-with-yices2 bvdiv-by-0
                        '(equal (bvdiv 32 x 0)
                                0))

(must-prove-with-yices2 bvmod-by-0
                        '(equal (bvmod 32 x 0)
                                (bvchop 32 x)))

(must-prove-with-yices2 sbvdiv-by-0
                        '(equal (sbvdiv 32 x 0)
                                0))

(must-prove-with-yices2 sbvrem-by-0
                        '(equal (sbvrem 32 x 0)
                                (bvchop 32 x)))

(must-not-prove-with-yices2 array-out-of-bounds-test
                            '(equal (bv-array-read 8 10 15
                                                   (bv-array-write 8 10 15 7
                                                                   '(0 0 0 0 0 0 0 0 0 0)))
                                    7)
                            :counterexample t)

(must-prove-with-yices2 array-padding-test
                        '(equal (bv-array-read 8 10 0
                                               (bv-array-write 5 10 0 7
                                                               '(0 0 0 0 0 0 0 0 0 0)))
                                7))

(must-not-prove-with-yices2 array-var-test
                            '(implies (and (true-listp x)
                                           (equal 10 (len x))
                                           (all-unsigned-byte-p 8 x))
                                      (equal (bv-array-read 8 10 5 x)
                                             77))
                            :counterexample t)

(must-prove-with-yices2 leftrotate-example
                        '(equal (leftrotate32 1 x)
                                (leftrotate32 33 x)))

(must-prove-with-yices2 leftrotate-example2
                        '(equal (leftrotate32 32 x)
                                (bvchop 32 x)))
