; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

;what is this file??


;; 2. equality comparison

(defun log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defun log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))


;; 3. unsigned inequalities

(defun log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defun log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defun log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defun log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))


;; 4. signed inequalities

;; The following function is not generated by translate-rtl, it is only needed
;; for the definitions of comp2<, comp2<=, etc.
(defun comp2 (x n)
  (declare (xargs :guard (and (rationalp x) (integerp n))))
  (if (< x (expt 2 (1- n)))
      x
    (- (- (expt 2 n) x))))

(defun comp2< (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log< (comp2 x n) (comp2 y n)))

(defun comp2<= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log<= (comp2 x n) (comp2 y n)))

(defun comp2> (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log> (comp2 x n) (comp2 y n)))

(defun comp2>= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log>= (comp2 x n) (comp2 y n)))


;; 5. unary logical operations

;make separate books for these? logior1 has one?
(defun logand1 (x n)
  (declare (xargs :guard (integerp n)))
  (log= x (1- (expt 2 n))))

(defun logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defun logxor1 (src)
  (declare (xargs :guard (integerp src)))
  (if (oddp (logcount src)) 1 0))




;should rtl.lisp disable these fns?


;; log<

(defthm log<-bvecp
  (bvecp (log< x y) 1)
  :hints (("Goal" :in-theory (enable log<))))

(defthm log<-nonnegative-integer-type
  (and (integerp (log< x y))
       (<= 0 (log< x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log<))))

;this rule is no better than log<-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<)))

;just a rewrite rule
(defthm log<-natp
  (natp (log< x y)))



;; log<=

(defthm log<=-bvecp
  (bvecp (log<= x y) 1)
  :hints (("Goal" :in-theory (enable log<=))))

(defthm log<=-nonnegative-integer-type
  (and (integerp (log<= x y))
       (<= 0 (log<= x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log<=))))

;this rule is no better than log<=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<=)))

;just a rewrite rule
(defthm log<=-natp
  (natp (log<= x y)))


;; log>

(defthm log>-bvecp
  (bvecp (log> x y) 1)
  :hints (("Goal" :in-theory (enable log>))))

(defthm log>-nonnegative-integer-type
  (and (integerp (log> x y))
       (<= 0 (log> x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log>))))

;this rule is no better than log>-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log>)))

;just a rewrite rule
(defthm log>-natp
  (natp (log> x y)))




;; log>=

(defthm log>=-bvecp
  (bvecp (log>= x y) 1)
  :hints (("Goal" :in-theory (enable log>=))))

(defthm log>=-nonnegative-integer-type
  (and (integerp (log>= x y))
       (<= 0 (log>= x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log>=))))

;this rule is no better than log>=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log>=)))

;just a rewrite rule
(defthm log>=-natp
  (natp (log>= x y)))


;; log=

(defthm log=-bvecp
  (bvecp (log= x y) 1)
  :hints (("Goal" :in-theory (enable log=))))

(defthm log=-nonnegative-integer-type
  (and (integerp (log= x y))
       (<= 0 (log= x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log=))))

(defthm log=-commutative
  (equal (log= x y)
         (log= y x)))

;this rule is no better than log=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log=)))

;just a rewrite rule
(defthm log=-natp
  (natp (log= x y)))


;; log<>

(defthm log<>-bvecp
  (bvecp (log<> x y) 1)
  :hints (("Goal" :in-theory (enable log<>))))

(defthm log<>-nonnegative-integer-type
  (and (integerp (log<> x y))
       (<= 0 (log<> x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable log<>))))

;this rule is no better than log<>-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<>)))

;just a rewrite rule
(defthm log<>-natp
  (natp (log<> x y)))

(defthm log<>-commutative
  (equal (log<> x y)
         (log<> y x)))


;; logand1

(defthm logand1-bvecp
  (bvecp (logand1 x y) 1)
  :hints (("Goal" :in-theory (enable logand1))))

(defthm logand1-nonnegative-integer-type
  (and (integerp (logand1 x y))
       (<= 0 (logand1 x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand1))))

;this rule is no better than logand1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logand1)))

;just a rewrite rule
(defthm logand1-natp
  (natp (logand1 x y)))


;; logior1
(defthm logior1-bvecp
  (bvecp (logior1 x) 1)
  :hints (("Goal" :in-theory (enable logior1))))

(defthm logior1-nonnegative-integer-type
  (and (integerp (logior1 x))
       (<= 0 (logior1 x)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logior1))))

;this rule is no better than logior1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logior1)))

;just a rewrite rule
(defthm logior1-natp
  (natp (logior1 x)))


;; logxor1

(defthm logxor1-bvecp
  (bvecp (logxor1 x) 1)
  :hints (("Goal" :in-theory (enable logxor1))))

(defthm logxor1-nonnegative-integer-type
  (and (integerp (logxor1 x))
       (<= 0 (logxor1 x)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logxor1))))

;this rule is no better than logxor1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logxor1)))

;just a rewrite rule
(defthm logxor1-natp
  (natp (logxor1 x)))




