; Shared comparison tests for the STP and Yices2 SMT backends
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp, uses-yices2)

(include-book "smt-backend-comparison" :ttags :all)

(compare-smt-backends commutative-bvxor
                      '(equal (bvxor 32 x y)
                              (bvxor 32 y x)))

(compare-smt-backends non-commutative-bvxor
                      '(equal (bvxor 32 x y)
                              (bvxor 32 x x))
                      :counterexample t)

(compare-smt-backends bvsx-32-16-def
                      '(implies (unsigned-byte-p 64 x)
                                (equal (bvsx 32 16 x)
                                       (bvif 32
                                             (equal 1 (getbit 15 x))
                                             (bvcat 16 65535 16 (bvsx 32 16 x))
                                             (bvsx 32 16 x)))))

(compare-smt-backends bvdiv-by-0
                      '(equal (bvdiv 32 x 0)
                              0))

(compare-smt-backends bvmod-by-0
                      '(equal (bvmod 32 x 0)
                              (bvchop 32 x)))

(compare-smt-backends sbvdiv-by-0
                      '(equal (sbvdiv 32 x 0)
                              0))

(compare-smt-backends sbvrem-by-0
                      '(equal (sbvrem 32 x 0)
                              (bvchop 32 x)))

(compare-smt-backends array-out-of-bounds-test
                      '(equal (bv-array-read 8 10 15
                                             (bv-array-write 8 10 15 7
                                                             '(0 0 0 0 0 0 0 0 0 0)))
                              7)
                      :counterexample t)

(compare-smt-backends array-padding-test
                      '(equal (bv-array-read 8 10 0
                                             (bv-array-write 5 10 0 7
                                                             '(0 0 0 0 0 0 0 0 0 0)))
                              7))

(compare-smt-backends array-var-test
                      '(implies (and (true-listp x)
                                     (equal 10 (len x))
                                     (all-unsigned-byte-p 8 x))
                                (equal (bv-array-read 8 10 5 x)
                                       77))
                      :counterexample t)

(compare-smt-backends leftrotate-example
                      '(equal (leftrotate32 1 x)
                              (leftrotate32 33 x)))

(compare-smt-backends leftrotate-example2
                      '(equal (leftrotate32 32 x)
                              (bvchop 32 x)))
