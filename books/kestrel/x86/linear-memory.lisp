; Rules about memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; Some theorems about linear memory operations in the x86 model, including RB,
;; RB-1, RML-size, and RML-<xx> where <xx> is 08/16/32/48/64/80/128.

(include-book "projects/x86isa/machine/linear-memory" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system) ; todo: use byte-listp instead below?
(include-book "kestrel/bv/bvcat" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for slice-too-high-is-0-new (todo: move it)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable rb rb-1 rml-size))

;move
(defthm unsigned-byte-p-of-0
  (equal (unsigned-byte-p size 0)
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm mv-nth-0-of-rb-1-of-xw
  (implies (not (equal :mem fld))
           (equal (mv-nth 0 (rb-1 n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb-1) (x86p-xw)))))

(defthm mv-nth-0-of-rb-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rb n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb) (rb-1)))))

(defthm mv-nth-0-of-rml-size-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rml-size
                                   rml16
                                   rml32
                                   rml48
                                   rml64
                                   rml80
                                   rml128)
                                  ()))))

;TODO: The r-x param of rb-1 is irrelevant (drop it?)
;; This clearly shows that the param is irrelevant, but this would loop as a rewrite rule.
(defthm rb-1-rx-irrel
  (equal (rb-1 n addr r-x     x86)
         (rb-1 n addr r-x-alt x86))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rb-1))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.
(defthm rb-1-when-not-r
  (implies (not (eq :r r-x))
           (equal (rb-1 n addr r-x x86)
                  (rb-1 n addr :r x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

;avoids all the special cases in rml-size
(defthm rml-size-becomes-rb
  (implies (and (app-view x86)
                (canonical-address-p addr)
                (canonical-address-p (+ -1 addr nbytes)))
           (equal (rml-size nbytes addr r-x x86)
                  (rb nbytes addr r-x x86)))
  :hints (("Goal" :in-theory (enable rml-size
                                     rml08
                                     rml16
                                     rml32
                                     rml48
                                     rml64
                                     rml80
                                     rml128))))

(defthm mv-nth-1-of-rml-size-of-0
  (equal (mv-nth 1 (rml-size 0 addr r-x x86))
         0)
  :hints (("Goal" :in-theory (enable rml-size))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.
(defthm mv-nth-1-of-rb-1-when-not-natp-cheap
  (implies (not (natp n))
           (equal (mv-nth 1 (rb-1 n addr r-x x86))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable rb-1))))

; better than x86isa::size-of-rb-1
(defthm unsigned-byte-p-of-mv-nth-1-of-rb-1
  (implies (and (<= (* 8 n) m)
                (natp m)
                (x86p x86))
           (unsigned-byte-p m (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :use (:instance size-of-rb-1 (m (* 8 n)))
           :in-theory (e/d (ash ifix)
                           (size-of-rb-1)))))

(defthm mv-nth-2-of-rb-1-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb-1 n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-2-of-rb-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb))))

(defthm mv-nth-2-of-rml08-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml08 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml08))))

(defthm mv-nth-2-of-rml16-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml16 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml16))))

(defthm mv-nth-2-of-rml32-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml32 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml32))))

(defthm mv-nth-2-of-rml48-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml48 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml48))))

(defthm mv-nth-2-of-rml64-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml64 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml64))))

(defthm mv-nth-2-of-rml80-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml80 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml80))))

(defthm mv-nth-2-of-rml128-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml128 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml128))))

(defthm mv-nth-2-of-rml-size-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml-size nbytes addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Material on combine-bytes is here because it is defined in projects/x86isa/machine/linear-memory.lisp

;; (defthm byte-listp-becomes-all-unsigned-byte-p
;;   (equal (byte-listp bytes)
;;          (and (acl2::all-unsigned-byte-p 8 bytes)
;;               (true-listp bytes)))
;;   :hints (("Goal" :in-theory (enable acl2::all-unsigned-byte-p byte-listp))))

(defun combine-bytes-n-induct (bytes n)
  (if (endp bytes)
      (list bytes n)
      (combine-bytes-n-induct (cdr bytes) (+ -8 n))))

(defthm unsigned-byte-p-of-combine-bytes-better
  (implies (and (acl2::all-unsigned-byte-p 8 bytes)
                (natp n)
                (>= n (* 8 (len bytes))))
           (unsigned-byte-p n (combine-bytes bytes)))
  :hints (("Goal" :induct (combine-bytes-n-induct bytes n)
           :in-theory (e/d (combine-bytes)
                           (x86isa::natp-combine-bytes ;bad (forcing)
                            )))))

;not true.  gross!
;; (DEFTHM NATP-COMBINE-BYTES-better
;;   (NATP (COMBINE-BYTES BYTES))
;;   :RULE-CLASSES :TYPE-PRESCRIPTION
;;   :hints (("Goal" :in-theory (e/d (COMBINE-BYTES) ( NATP-COMBINE-BYTES)))))

;; (DEFTHM ACL2::UNSIGNED-BYTE-P-LOGIOR-better
;;   (IMPLIES (AND ;(FORCE (INTEGERP I))
;;                 (FORCE (INTEGERP J)))
;;            (EQUAL (UNSIGNED-BYTE-P ACL2::SIZE (LOGIOR I J))
;;                   (AND (UNSIGNED-BYTE-P ACL2::SIZE I)
;;                        (UNSIGNED-BYTE-P ACL2::SIZE J))))
;;   :hints (("Goal"
;;            :use (:instance ACL2::UNSIGNED-BYTE-P-LOGIOR (i (ifix i)))
;;            :in-theory (e/d (LOGIOR ifix) ( ACL2::UNSIGNED-BYTE-P-LOGIOR
;;                                              ACL2::LOGNOT-OF-LOGAND))))
;; )

;also uses better bvops
(defthmd combine-bytes-unroll-better
  (implies (and (not (endp bytes))
                (true-listp bytes) ;todo drop
                (acl2::all-unsigned-byte-p 8 bytes))
           (equal (combine-bytes bytes)
                  (acl2::bvcat (* 8 (- (len bytes) 1))
                               (combine-bytes (cdr bytes))
                               8
                               (car bytes)
                               )))
  :hints (("Goal" :induct (COMBINE-BYTES BYTES)
           :expand (COMBINE-BYTES BYTES)
           :in-theory (e/d (COMBINE-BYTES
                            (:induction combine-bytes)
                            ACL2::SLICE-TOO-HIGH-IS-0-NEW)
                           (;ACL2::UNSIGNED-BYTE-P-LOGIOR ;caused forcing
                            )))))

(defthm unsigned-byte-p-of-combine-bytes-lemma
  (implies (byte-listp bytes)
           (unsigned-byte-p (* 8 (len bytes))
                            (combine-bytes bytes)))
  :hints (("Goal" :in-theory (enable combine-bytes byte-listp))))




;; ;replace the other one!
;; (encapsulate ()
;;   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;;   (defthm slice-of-times-of-expt-gen
;;     (implies (and            ;(<= j n) ;drop?
;;               (integerp x)   ;drop?
;;               (natp n)
;;               (natp j)
;;               (natp m))
;;              (equal (slice m n (* (expt 2 j) x))
;;                     (slice (- m j) (- n j) x)))
;;     :hints (("Goal" :in-theory (e/d (slice logtail nfix) ())))))

;move
;; ;avoids having to give a highsize
;; (defthm slice-of-logapp
;;   (implies (and (natp lowsize)
;;                 (natp low)
;;                 (natp high)
;;                 (integerp highval))
;;            (equal (slice high low (logapp lowsize lowval highval))
;;                   (slice high low (bvcat (+ 1 high (- lowsize)) highval lowsize lowval))))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance ACL2::BVCAT-RECOMBINE
;;                                   (acl2::lowsize lowsize)
;;                                   (acl2::lowval lowval)
;;                                   (acl2::highval highval)
;;                                   (acl2::highsize (+ 1 high (- lowsize)))))))


;;   :hints (("Goal" :in-theory (e/d (;bvcat logapp
;;                                          ;acl2::slice-of-sum-cases
;;                                          )
;;                                   (acl2::slice-of-*)))))

;move
(defthm slice-of-logapp-case-1
  (implies (and (natp high)
                (natp low)
                (natp lowsize)
                (<= lowsize low) ; this case
                (unsigned-byte-p lowsize lowval)
                (integerp highval))
           (equal (acl2::slice high low (logapp lowsize lowval highval))
                  (acl2::slice (+ (- lowsize) high) (+ (- lowsize) low) highval)))
  :hints (("Goal" :in-theory (e/d (acl2::slice logapp) (acl2::logtail-of-plus
                                                  acl2::unsigned-byte-p-of-logapp-large-case))
           :use (:instance acl2::unsigned-byte-p-of-logapp-large-case
                           (size1 low)
                           (size lowsize)
                           (i lowval)
                           (j (acl2::BVCHOP (+ LOW (- LOWSIZE)) HIGHVAL))))))

(defthm slice-of-combine-bytes
  (implies (and (natp n)
                (< n (len bytes))
                (byte-listp bytes) ;too bad
                )
           (equal (acl2::slice (+ 7 (* 8 n)) (* 8 n) (x86isa::combine-bytes bytes))
                  (acl2::bvchop 8 (nth n bytes))))
  :hints (("Goal" :in-theory (e/d (x86isa::combine-bytes
                                   ACL2::BVCAT-RECOMBINE
                                   ;;logapp
                                   ;;ACL2::SLICE-OF-SUM-CASES
                                   (:i nth)
                                   BYTE-LISTP)
                                  (;acl2::nth-of-cdr
                                   )))))
