; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(include-book "pp-flatten-meta-fncs")

(include-book "pp-flatten-with-binds-meta")

(include-book "std/util/defines" :dir :system)

(include-book "sum-merge-fncs")

(local
 (fetch-new-theory
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (in-theory (disable +-IS-SUM)))

(local
 (set-induction-depth-limit 1))

(acl2::Defines
  search-for-c-with-hash
  (define search-for-c-with-hash (term hash-code (limit natp))
    :measure (nfix limit)
    (cond
     ((zp limit)
      nil)
     (t (case-match term
          (('c hash1 arg1 arg2 arg3)
           (or (equal hash1 hash-code)
               (search-for-c-with-hash arg1 hash-code (1- limit))
               (search-for-c-with-hash arg2 hash-code (1- limit))
               (search-for-c-with-hash arg3 hash-code (1- limit))))
          (& (and (consp term)
                  (search-for-c-with-hash-lst (cdr term) hash-code (1-
                                                                    limit))))))))

  (define search-for-c-with-hash-lst (lst hash-code (limit natp))
    :measure (nfix limit)
    (and (not (zp limit))
         (consp lst)
         (or (search-for-c-with-hash (car lst) hash-code (1- limit))
             (search-for-c-with-hash-lst (cdr lst) hash-code (1- limit))))))

(define negated-termp (term)
  :inline t
  (case-match term (('-- &) t))
  ///
  (defthm NEGATED-TERMP-implies
    (implies (NEGATED-TERMP term)
             (case-match term (('-- &) t)))
    :rule-classes :forward-chaining))

(progn
  (encapsulate
    (((stingy-pp-clean) => *)
     )
    (local
     (defun stingy-pp-clean ()
       nil))

    )

  (define return-t ()
    t)
  (define return-nil ()
    nil)

  (defmacro enable-stingy-pp-clean (enabled)
    (if enabled
        `(defattach  stingy-pp-clean return-t)
      `(defattach  stingy-pp-clean return-nil)))

  (enable-stingy-pp-clean nil)

  (define clean-pp-args-cond (s-lst c-lst)
    (cond
     #|((unpack-booth-later-enabled)
     nil)|#
     ((stingy-pp-clean)
      (and (equal s-lst nil)
           (or (atom c-lst)
               (atom (cdr c-lst))
               ;;(atom (cddr c-lst))
               )))
     (t t)))
  )

(define get-c-args ((c rp-termp))
  :inline t
  :returns (mv (hash-code integerp)
               (s-args rp-termp
                       :hyp (rp-termp c))
               (pp-args rp-termp
                        :hyp (rp-termp c))
               (c-arg-lst rp-term-listp
                          :hyp (rp-termp c))
               (valid symbolp))
  (b* ((c (ex-from-rp$ c)))
    (case-match c
      (('c ('quote hash-code) s pp ('list . c-lst))
       (mv (if (consp hash-code) (ifix (car hash-code)) (ifix hash-code))
           s pp c-lst 'c))
      (('c ('quote hash-code) s pp ''nil)
       (mv (if (consp hash-code) (ifix (car hash-code)) (ifix hash-code))
           s pp nil 'c))
      (& (mv 0 ''nil ''nil nil nil)))))

(defsection hash-codes

  (local
   (use-ihs-logops-lemmas t))

  (define hash-coef ()
    :inline t
    13)

  (local
   (defthm cons-count-of-ex-from-rp/--loose
     (and (<= (cons-count (EX-FROM-RP/--LOOSE x))
              (cons-count x))
          (implies (consp (EX-FROM-RP/--LOOSE x))
                   (and (O< (CONS-COUNT (CADR (EX-FROM-RP/--LOOSE x)))
                            (CONS-COUNT x)))))
     :hints (("Goal"
              :induct (EX-FROM-RP/--LOOSE x)
              :do-not-induct t
              :in-theory (e/d (EX-FROM-RP/--LOOSE
                               o<
                               cons-count)
                              ())))))

  (define binary-fnc-hash (term)
    :returns (hash integerp)
    :measure (cons-count term)

    :hints (("Goal"
             :in-theory (e/d (measure-lemmas) ())))
    (b* ((term (ex-from-rp/--loose term)))
      (cond ((atom term)
             0)
            ((quotep term)
             (if (and (consp (cdr term))
                      (integerp (cadr term)))
                 (cadr term)
               0))
            ((binary-not-p term)
             (+ 5
                (binary-fnc-hash (cadr term))))
            ((or (binary-and-p term)
                 (binary-or-p term)
                 (binary-xor-p term))
             (+ 5
                (binary-fnc-hash (caddr term))
                (binary-fnc-hash (cadr term))))
            ((binary-?-p term)
             (+ 5
                (binary-fnc-hash (cadddr term))
                (binary-fnc-hash (caddr term))
                (binary-fnc-hash (cadr term))))
            ((single-c-p term)
             (ifix (and (quotep (cadr term))
                        (consp (cdr (cadr term)))
                        (consp (unquote (cadr term)))
                        (car (unquote (cadr term))))))
            ((single-s-p term)
             (ifix (and (quotep (cadr term))
                        (consp (cdr (cadr term)))
                        (unquote (cadr term)))))
            ((logbit-p term)
             (ifix (and (quotep (caddr term))
                        (consp (cdr (caddr term)))
                        (unquote (caddr term)))))
            (t 0))))

  (define pp-instance-hash (e)
    :returns (hash integerp)
    :inline t
    (case-match e
      (('and-list ('quote hash) &)
       (ifix hash))
      (('-- ('and-list ('quote hash) &))
       (ifix hash))
      (''1
       1)
      (''1
       1)
      (&
       (if (binary-fnc-p (ex-from-rp e))
           (binary-fnc-hash e)
         0)
       )))

  (defwarrant pp-instance-hash$inline)

  (define pp-lst-hash ((pp-lst rp-term-listp))
    ;;:inline t
    :returns (hash-code integerp)
    (if (atom pp-lst)
        0                             
      (+ (pp-instance-hash (car pp-lst))
         (pp-lst-hash (cdr pp-lst)))))

  (define calculate-pp-hash ((pp rp-termp))
    :returns (hash-code integerp)
    :inline t
    (case-match pp
      (('list . pp-lst)
       ;;(let ((len (len pp-lst))) (* len len))
       (pp-lst-hash pp-lst)
       )
      (& 0)))

  (defwarrant calculate-pp-hash$inline)

  (define get-hash-code-of-single-s (s)
    :returns (hash-code integerp)
    :inline t
    (b* ((s (ex-from-rp/--loose s)))
      (case-match s
        (('s ('quote hash-code) & &)
         (ifix hash-code))
        (''0
         0)
        (&
         (progn$ (hard-error
                  'get-hash-code-of-single-s
                  "unrecognized s instance in get-hash-code-of-s:~p0 ~%"
                  (list (cons #\0 s)))
                 0)))))

  (defwarrant get-hash-code-of-single-s$inline)
  (defwarrant acl2::logcar$inline)

  (define get-hash-code-of-s-lst ((lst true-listp))
    :returns (mv (hash-code1 integerp)
                 (hash-code2 integerp))
    ;;:inline t ;; or should it be inline?
    (b* (((when (atom lst)) (mv 0 0))
         ((mv r1 r2)
          (get-hash-code-of-s-lst (cdr lst)))
         (h (get-hash-code-of-single-s (car lst))))
      (mv (+ r1 h) (ifix (+ r2 (logcar h))))))

  ;; (defwarrant get-hash-code-of-s-lst$inline)

  (define get-hash-code-of-s ((s rp-termp))
    :returns (mv (hash-code1 integerp)
                 (hash-code2 integerp))
    :inline t
    (case-match s
      (('list . s-lst)
       (get-hash-code-of-s-lst s-lst))
      (& (mv 0 0))))

  (defwarrant get-hash-code-of-s$inline)

  (define get-hash-code-of-single-c (c)
    :returns (hash-code integerp)
    :inline t
    (b* ((c (ex-from-rp/--loose c)))
      (case-match c
        (('c ('quote hash-code) & & &)
         (if (consp hash-code)
             (ifix (cdr hash-code))
           (ifix hash-code)))
        (''0
         0)
        (& (progn$ (hard-error
                    'get-hash-code-of-single-c
                    "unrecognized c instance:~p0 ~%"
                    (list (cons #\0 c)))
                   0)))))

  (defwarrant get-hash-code-of-single-c$inline)

  (define get-hash-code-of-c-lst ((c-lst true-listp)
                                  ;;&optional
                                  ;;((cnt natp) '0)
                                  )
    :returns (hash-code integerp)
    ;;:inline t
    (if (atom c-lst)
        0 ;
      (+ (ifix (ash (get-hash-code-of-single-c (car c-lst)) -1))
         (get-hash-code-of-c-lst (cdr c-lst)))))

  (define get-hash-code-of-c ((c rp-termp))
    :returns (hash-code integerp)
    :inline t
    (case-match c
      (('list . c-lst)
       (get-hash-code-of-c-lst c-lst))
      (& 0)))

  (define calculate-s-hash ((pp rp-termp)
                            (c rp-termp))
    :guard-hints (("Goal"
                   :in-theory (e/d () (loghead unsigned-byte-p))))
    :returns (hash-code integerp)
    (the (unsigned-byte 59)
      (loghead 59
               (* (hash-coef)
                  (+ (* 3 (calculate-pp-hash pp))
                     (* 7 (get-hash-code-of-c c)))))))

  (local
   (defthm integerp-of-+and*
     (implies (and (integerp x)
                   (integerp y))
              (and (integerp (+ x y))
                   (integerp (* x y))))))

  (define calculate-c-hash ((s rp-termp)
                            (pp rp-termp)
                            (c rp-termp))
    :returns (hash-code)
    :guard-hints (("Goal"
                   :in-theory (e/d () (ash logapp loghead unsigned-byte-p))))
    (b* ((?hash-code-base (calculate-s-hash pp c))
         ((mv ?s-hash-codes1 ?s-hash-codes2)
          (get-hash-code-of-s s))

         (hash-coef (the (unsigned-byte 8) (hash-coef)))

         (mult0 (the (unsigned-byte 90)
                  (loghead 90
                           (* hash-coef
                              (logxor (loghead 90 hash-code-base)
                                      (loghead 90 (ash hash-code-base -90)))))))

         ;; expecting below to be zero in cases where c-of-s simplification is
         ;; enabled (which is the default)
         (mult1 (the (unsigned-byte 59)
                  (loghead 59 (* s-hash-codes1 hash-coef))))
         (mult2 (the (unsigned-byte 59)
                  (loghead 59 (* s-hash-codes2 hash-coef)))))
      (cons
       (the (unsigned-byte 59)
         (logapp 8 (len (list-to-lst pp))
                 (logapp 8 (len (list-to-lst c))
                         (loghead 43 (ash (the (unsigned-Byte 90)
                                            (loghead 90 (+ mult0 mult1))) ;
                                          -47)))))
       (the (unsigned-byte 59) (loghead 59 (+ mult0 mult2)))
       ))))

(local
 (in-theory (disable rp-termp)))

(local
 (defthm measure-lemma-loose1
   (implies (and
             (consp (ex-from-rp max-term))
             (consp (cdr (ex-from-rp max-term)))
             (not (cddr (ex-from-rp max-term))))
            (o< (cons-count (cadr (ex-from-rp max-term)))
                (cons-count max-term)))
   :hints (("goal"
            :induct (ex-from-rp max-term)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:rewrite measure-lemma1)
                             (:rewrite cons-count-atom)
                             (:rewrite default-cdr)
                             (:rewrite measure-lemma6-5)
                             (:definition ex-from-rp)
                             (:rewrite measure-lemma1-2)))))))
(local
 (defthm measure-lemma-loose2
   (implies (and  (consp (ex-from-rp max-term))
                  (consp (cdr (ex-from-rp max-term)))
                  (consp (cddr (ex-from-rp max-term)))
                  (consp (cdddr (ex-from-rp max-term)))
                  (consp (cddddr (ex-from-rp max-term)))
                  (not (cdr (cddddr (ex-from-rp max-term)))))
            (o< (cons-count (cdr (car (cddddr (ex-from-rp max-term)))))
                (cons-count max-term)))
   :hints (("goal"
            :induct (ex-from-rp max-term)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:rewrite default-cdr)
;(:rewrite ex-from-rp-loose-is-rp-termp)
                             (:definition rp-termp)
                             (:rewrite measure-lemma1-2)
                             (:rewrite measure-lemma1)))))))

(local
 (defthm measure-lemma-loose3
   (IMPLIES (AND  (CONSP (ex-from-rp MAX-TERM))
                  (CONSP (CDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDDR (ex-from-rp MAX-TERM)))
                  (NOT (CDR (CDDDDR (ex-from-rp MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDDR (ex-from-rp MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)
                             (:REWRITE DEFAULT-CAR)
                             ;;                             (:REWRITE ACL2::O<=-O-FINP-DEF)
                             ))))))

(local
 (defthm measure-lemma-loose4
   (IMPLIES (AND  (CONSP (ex-from-rp MAX-TERM))
                  (CONSP (CDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDR (ex-from-rp MAX-TERM)))
                  (CONSP (CDDDDR (ex-from-rp MAX-TERM)))
                  (NOT (CDR (CDDDDR (ex-from-rp MAX-TERM)))))
            (O< (CONS-COUNT (CDR (CADDR (ex-from-rp MAX-TERM))))
                (CONS-COUNT MAX-TERM)))
   :hints (("Goal"
            :induct (ex-from-rp MAX-TERM)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp
                             measure-lemmas)
                            ((:REWRITE DEFAULT-CDR)
                             (:REWRITE MEASURE-LEMMA1)
                             (:REWRITE MEASURE-LEMMA1-2)

                             (:REWRITE DEFAULT-CAR)
                             ;;                             (:REWRITE ACL2::O<=-O-FINP-DEF)

                             ))))))
(local
 (defthm local-measure-lemma4
   (implies (and
             (integerp term1)
             (integerp term2)
             (integerp term3)
             (o<= term2 term3)
             (o< term1 term2))
            (o< term1 term3))
   :hints (("Goal"
            :in-theory (e/d (o<) ())))))

(local
 (defthm local-measure-lemma5
   (implies (and (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (consp (cdddr term))
                 (consp (cddddr term))
                 (consp (car (cddddr term)))
                 (not (cdr (cddddr term))))
            (o< (cons-count (cdr (car (cddddr term))))
                (cons-count term)))
   :hints (("Goal"
            :in-theory (e/d (cons-count) ())))))

(local
 (defthm local-measure-lemma6
   (implies (and (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (consp (cdddr term))
                 (consp (car (cdddr term)))
                 (not (cdr (cdddr term))))
            (o< (cons-count (cdr (car (cdddr term))))
                (cons-count term)))
   :hints (("Goal"
            :in-theory (e/d (cons-count) ())))))

(local
 (defthm local-measure-lemma7
   (implies (and (consp (ex-from-rp term))
                 (consp (cdr (ex-from-rp term)))
                 (consp (cddr (ex-from-rp term)))
                 (consp (cdddr (ex-from-rp term)))
                 (consp (cddddr (ex-from-rp term)))
                 (consp (car (cddddr (ex-from-rp term))))
                 (not (cdr (cddddr (ex-from-rp term)))))
            (o< (cons-count (cdr (car (cddddr (ex-from-rp term)))))
                (cons-count term)))
   :hints (("goal"
            :use ((:instance local-measure-lemma5 (term (ex-from-rp term)))
                  (:instance local-measure-lemma4
                             (term1 (CONS-COUNT (CDR (CAR (CDDDDR (ex-from-rp TERM))))))
                             (term2 (CONS-COUNT (ex-from-rp TERM)))
                             (term3 (CONS-COUNT TERM))))
            :in-theory (e/d (measure-lemmas)
                            (local-measure-lemma5 local-measure-lemma4))))))

(local
 (defthm local-measure-lemma8
   (implies (and (consp (ex-from-rp term))
                 (consp (cdr (ex-from-rp term)))
                 (consp (cddr (ex-from-rp term)))
                 (consp (cdddr (ex-from-rp term)))
                 (consp (car (cdddr (ex-from-rp term))))
                 (not (cdr (cdddr (ex-from-rp term)))))
            (o< (cons-count (cdr (car (cdddr (ex-from-rp term)))))
                (cons-count term)))
   :hints (("goal"
            :use ((:instance local-measure-lemma6 (term (ex-from-rp term)))
                  (:instance local-measure-lemma4
                             (term1 (CONS-COUNT (CDR (CAR (CDDDR (ex-from-rp TERM))))))
                             (term2 (CONS-COUNT (ex-from-rp TERM)))
                             (term3 (CONS-COUNT TERM))))
            :in-theory (e/d (measure-lemmas) (local-measure-lemma4 local-measure-lemma6))))))

(local
 (defthm local-measure-lemma10
   (IMPLIES (AND (consp (ex-from-rp TERM)))
            (O< (CONS-COUNT (CDR (ex-from-rp TERM)))
                (CONS-COUNT TERM)))
   :hints (("Goal"
            :in-theory (e/d (measure-lemmas) ())))))

(local
 (defthm local-measure-lemma11
   (implies (and
             (consp (ex-from-rp term)))
            (o< 1 (cons-count term)))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp cons-count) ())))))

(local
 (in-theory (disable ex-from-rp
                     (:definition acl2::apply$-badgep)
                     (:linear acl2::apply$-badgep-properties . 1)
                     (:definition subsetp-equal)
                     (:definition member-equal)
                     (:rewrite
                      acl2::member-equal-newvar-components-1)
                     (:definition rp-term-listp)
                     include-fnc)))

(local
 (defthm single-c-p-rp-term-listp-lemma
   (implies (and (single-c-p term)
                 (rp-termp term)
                 (equal (car (car (cddddr term)))
                        'list))
            (rp-term-listp (cdr (car (cddddr term)))))
   :hints (("goal"
            :expand ((rp-termp term)
                     (rp-term-listp (cddddr term))
                     (rp-termp (car (cddddr term)))
                     (rp-term-listp (cddr term))
                     (rp-term-listp (cdddr term))
                     (rp-term-listp (cdr term)))
            :in-theory (e/d (rp-term-listp
                             single-c-p)
                            ())))))

(local
 (defthm dummy-rp-term-listp-lemma
   (implies (and (rp-term-listp lst) (consp lst))
            (rp-termp (car lst)))
   :hints (("goal"
            :in-theory (e/d (rp-termp rp-term-listp) ())))))

(acl2::defines
  get-max-min-val
  :flag-defthm-macro defthm-get-min-max-val
  :flag-local nil
  :prepwork ((local
              (in-theory (e/d (measure-lemmas
                               list-to-lst)
                              (measure-lemma1
                               measure-lemma1-2
                               ;;                              (:rewrite acl2::o-p-o-infp-car)
                               (:rewrite default-car)
                               not-include-rp)))))

  :verify-guards nil
  (define get-max-min-val ((term rp-termp))
    :measure (cons-count term)
    :returns (mv  (max-val integerp)
                  (min-val integerp)
                  (valid booleanp))
    (b* (((when (has-bitp-rp term)) (mv 1 0 t))
         (term (ex-from-rp$ term)))
      (cond
       ((single-c-p term)
        (b* (((mv s pp c)
              (case-match term (('c & s pp c) (mv s pp c)) (& (mv nil nil nil))))
             ((mv s-max-val s-min-val s-valid)
              (case-match s
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((mv pp-max-val pp-min-val pp-valid)
              (case-match pp
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((mv c-max-val c-min-val c-valid)
              (case-match c
                (('list . lst) (get-max-min-val-lst lst))
                (''nil (mv 0 0 t))
                (& (mv 0 0 nil))))
             ((unless (and s-valid pp-valid c-valid))
              (mv 0 0 nil)))
          (mv (floor (+ s-max-val pp-max-val c-max-val) 2)
              (floor (+ s-min-val pp-min-val c-min-val) 2)
              t)))
       ((or (single-s-p term)
            (binary-fnc-p term)
            (logbit-p term)
            (and-list-p term))
        (mv 1 0 t))
       ((equal term ''1) (mv 1 1 t))
       ((--.p term)
        (b* ((n (cadr term))
             ((mv max-val min-val valid)
              (get-max-min-val n)))
          (mv (- min-val) (- max-val) valid)))
       (t (mv 0 0 nil)))))
  (define get-max-min-val-lst ((lst rp-term-listp))
    :measure (cons-count lst)
    :returns (mv (max-val integerp)
                 (min-val integerp)
                 (valid booleanp))
    (if (atom lst)
        (mv 0 0 t)
      (b* (((mv max-val1 min-val1 valid1)
            (get-max-min-val (car lst)))
           ((unless valid1)
            (mv max-val1 min-val1 valid1))
           ((mv max-val2 min-val2 valid2)
            (get-max-min-val-lst (cdr lst))))
        (mv (+ max-val1 max-val2) (+ min-val1 min-val2) valid2))))

  ///
  (verify-guards get-max-min-val-lst
    :hints (("Goal"
             :in-theory (e/d (RP-TERM-LISTP) ())))))

(define len-lte (lst size)
  :guard (natp size)
  :returns (res-size)
  (if (atom lst)
      size
    (if (zp size)
        nil
      (len-lte (cdr lst) (1- size))))
  ///
  (defret natp-of-<fn>
    (implies (and (natp size)
                  res-size)
             (natp res-size))))

(acl2::defines
  maybe-bitp-precheck
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas
                            )
                           ())))
  :prepwork
  ((local
    (defthmd dummy-lemma0
      (implies (and (natp x)
                    (O< x (CONS-COUNT (ex-from-rp TERM))))
               (O< x (CONS-COUNT TERM)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp cons-count) ())))))

   (local
    (In-Theory (enable measure-lemmas)))

   (local
    (defthmd dummy-lemma1
      (implies (or #|(and (<= x y)
                (< y z))|#
                (and (< x y)
                     (<= y z)))
               (< x z))))

   (local
    (defthm 0<-to-<
      (implies (and (natp x) (natp y))
               (equal (O< x y)
                      (< x y)))
      :hints (("Goal"
               :expand (O< x y)
               :in-theory (e/d () ())))))

   (local
    (defthm dummy-lemma2
      (IMPLIES (AND (CONSP term)
                    (EQUAL (CAR term) 'C)
                    (CONSP (CDR term))
                    (CONSP (CDDR term))
                    (CONSP (CDDDR term))
                    (CONSP (CDDDDR term))
                    (NOT (CDR (CDDDDR term))))
               (O< (CONS-COUNT (LIST-TO-LST (CAR (CDDDDR term))))
                   (CONS-COUNT TERM)))
      :otf-flg t
      :hints (("Goal"

               :do-not-induct t
               :in-theory (e/d (LIST-TO-LST
                                cons-count)
                               ())))))

   (local
    (defthm dummy-lemma3
      (IMPLIES (AND (CONSP (EX-FROM-RP TERM))
                    (EQUAL (CAR (EX-FROM-RP TERM)) 'C)
                    (CONSP (CDR (EX-FROM-RP TERM)))
                    (CONSP (CDDR (EX-FROM-RP TERM)))
                    (CONSP (CDDDR (EX-FROM-RP TERM)))
                    (CONSP (CDDDDR (EX-FROM-RP TERM)))
                    (NOT (CDR (CDDDDR (EX-FROM-RP TERM)))))
               (O< (CONS-COUNT (LIST-TO-LST (CAR (CDDDDR (EX-FROM-RP TERM)))))
                   (CONS-COUNT TERM)))
      :otf-flg t
      :hints (("Goal"
               :use ((:instance dummy-lemma2
                                (term (ex-from-rp term)))
                     (:instance dummy-lemma1
                                (x (CONS-COUNT
                                    (LIST-TO-LST (CAR (CDDDDR
                                                       (EX-FROM-RP TERM))))))
                                (z (CONS-COUNT TERM))
                                (y (cons-count (EX-FROM-RP TERM)))))
               :do-not-induct t
               :in-theory (e/d () (dummy-lemma1 dummy-lemma2)))))))

  (define maybe-bitp-precheck ((term rp-termp)
                               &optional
                               ((upper-bound natp) '1))
    :verify-guards nil
    :returns (res)
    :measure (cons-count term)
    (b* (((when (has-bitp-rp term))
          (1- upper-bound))
         (term (ex-from-rp$ term)))
      (case-match term
        (('c & s pp c)
         (b* ((upper-bound (1+ (* 2 upper-bound)))
              (s-lst (list-to-lst s))
              (upper-bound (len-lte s-lst upper-bound))
              ((unless upper-bound) -1)
              (pp-lst (list-to-lst pp))
              (upper-bound (len-lte pp-lst upper-bound))
              ((unless upper-bound) -1)
              (c-lst (list-to-lst c)))
           (f2 (maybe-bitp-precheck-lst c-lst upper-bound))))
        (& -1))))
  (define maybe-bitp-precheck-lst ((lst rp-term-listp)
                                   (upper-bound natp))
    :measure (cons-count lst)
    :returns (res)
    (if (atom lst)
        upper-bound
      (b* ((upper-bound (maybe-bitp-precheck (car lst) upper-bound))
           ((when (equal upper-bound -1)) upper-bound)
           (upper-bound (maybe-bitp-precheck-lst (cdr lst) upper-bound)))
        upper-bound)))
  ///

  (defret-mutual result-of-maybe-bitp-precheck
    (defret natp-of-<fn>
      (implies (and (natp upper-bound)
                    (not (equal res -1)))
               (natp res))
      :fn maybe-bitp-precheck)
    (defret natp-of-<fn>
      (implies (and (natp upper-bound)
                    (not (equal res -1)))
               (natp res))
      :fn maybe-bitp-precheck-lst)
    :hints (("Goal"
             :in-theory (e/d (f2)
                             (FLOOR2-IF-F2)))))

  (verify-guards maybe-bitp-precheck-fn
    :hints (("Goal"
             :in-theory (e/d (rp-term-listp)
                             ())))))

(define is-c-bitp-traverse ((single-c rp-termp))
  :returns (res booleanp)
  (b* (((unless (natp (maybe-bitp-precheck single-c)))
        nil)
       ((mv max-val min-val valid)
        (get-max-min-val single-c)))
    (and
     valid
     (equal min-val 0)
     (equal max-val 1))))

;; a b c e
;; a b c d e

(local
 (defthm dummmy-rp-term-listp-lemma
   (implies (and (rp-term-listp x)
                 (consp x))
            (rp-term-listp (cdr x)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (rp-term-listp) ())))))

(progn
  (define pp-lst-subsetp ((pp-lst1 rp-term-listp)
                          (pp-lst2 rp-term-listp)
                          &key
                          (pp-flg 't))
    :measure (+ (cons-count pp-lst1)
                (cons-count pp-lst2))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    (b* (((when (atom pp-lst1)) t)
         ((when (atom pp-lst2)) (atom pp-lst1))
         (cur1 (car pp-lst1))
         (cur2 (car pp-lst2))
         ((mv order equals) (if pp-flg (pp-order cur1 cur2) (s-order cur1 cur2))))
      (cond (equals
             (pp-lst-subsetp (cdr pp-lst1) (cdr pp-lst2) :pp-flg pp-flg))
            (order nil)
            (t (pp-lst-subsetp pp-lst1 (cdr pp-lst2) :pp-flg pp-flg)))))

  (define pp-subsetp ((pp1 rp-termp)
                      (pp2 rp-termp)
                      &key
                      (pp-flg 't))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2)))
      (pp-lst-subsetp pp1-lst pp2-lst :pp-flg pp-flg))))

(progn
  (define and-lst-subsetp ((pp-lst1 rp-term-listp)
                           (pp-lst2 rp-term-listp))
    :measure (+ (cons-count pp-lst1)
                (cons-count pp-lst2))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    (b* (((when (atom pp-lst1)) t)
         ((when (atom pp-lst2)) (atom pp-lst1))
         (cur1 (car pp-lst1))
         (cur2 (car pp-lst2)))
      (cond ((rp-equal-cnt cur1 cur2 0)
             (and-lst-subsetp (cdr pp-lst1) (cdr pp-lst2)))
            ((lexorder2- cur1 cur2) nil)
            (t (and-lst-subsetp pp-lst1 (cdr pp-lst2))))))

  (define and-subsetp ((pp1 rp-termp)
                       (pp2 rp-termp))
    :guard-hints (("Goal"
                   :in-theory (e/d (RP-TERM-LISTP) ())))
    (b* ((pp1 (ex-from-rp$ pp1))
         (pp2 (ex-from-rp$ pp2))
         ((unless (and (or (case-match pp1 (('and-list & ('list . &)) t))
                           (logbit-p (ex-from-rp$ pp1)))
                       (or (case-match pp2 (('and-list & ('list . &)) t))
                           (logbit-p (ex-from-rp$ pp2)))))
          nil)

         (pp1-lst (if (logbit-p (ex-from-rp$ pp1))
                      (list (ex-from-rp$ pp1))
                    (cdr (caddr pp1))))
         (pp2-lst (if (logbit-p (ex-from-rp$ pp2))
                      (list (ex-from-rp$ pp2))
                    (cdr (caddr pp2)))))
      (and-lst-subsetp pp1-lst pp2-lst))))

(local
 (defthm rp-term-listp-of-cons
   (equal (rp-term-listp (cons a b))
          (and (rp-termp a)
               (rp-term-listp b)))
   :hints (("Goal"
            :in-theory (e/d (rp-term-listp) ())))))

(local
 (defthm rp-termp-of--
   (iff (rp-termp (list '-- a))
        (rp-termp a))
   :hints (("Goal"
            :expand (rp-termp (list '-- a))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp (cons 'list rest))
        (rp-term-listp rest))
   :hints (("Goal"
            :expand (rp-termp (cons 'list rest))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-of-s-and-c
   (and (iff (rp-termp (cons 's rest))
             (rp-term-listp rest))
        (iff (rp-termp (cons 'c rest))
             (rp-term-listp rest)))
   :hints (("Goal"
            :expand ((rp-termp (cons 's rest))
                     (rp-termp (cons 'c rest)))
            :in-theory (e/d () ())))))

(local
 (defthm rp-termp-car-cddddr
   (IMPLIES (AND (RP-TERMP TERM)
                 (CONSP TERM)
                 (NOT (QUOTEP TERM))
                 (CONSP (CDR TERM))
                 (CONSP (CDDR TERM))
                 (CONSP (CDDDR TERM))
                 (CONSP (CDDdDR TERM)))
            (RP-TERMP (CAr (cDdDDR TERM))))
   :hints (("Goal"
            :do-not-induct t
            :expand (RP-TERMP TERM)
            :in-theory (e/d (rp-termp
                             is-rp
                             rp-term-listp)
                            ())))))

(local
 (defthm rp-termp-of-consed
   (equal (rp-termp (cons sym rest))
          (let ((term  (cons sym rest)))
            (COND ((ATOM TERM) (AND (SYMBOLP TERM) TERM))
                  ((EQ (CAR TERM) 'QUOTE)
                   (AND (CONSP (CDR TERM))
                        (NULL (CDR (CDR TERM)))))
                  ((EQ (CAR TERM) 'RP)
                   (AND (IS-RP TERM)
                        (RP-TERMP (CADDR TERM))))
                  ((EQ (CAR TERM) 'FALIST)
                   (AND (FALIST-CONSISTENT TERM)
                        (RP-TERMP (CADDR TERM))))
                  (T (AND (SYMBOLP (CAR TERM))
                          (CAR TERM)
                          (RP-TERM-LISTP (CDR TERM)))))))
   :hints (("Goal"
            :expand (rp-termp (cons sym rest))
            :in-theory (e/d () ())))))

(progn
  (define abs-term (term)
    :inline t
    :returns (mv (abs rp-termp :hyp (rp-termp term))
                 (signed booleanp))
    (case-match term (('-- c1) (mv c1 t)) (& (mv term nil))))

  (define ligth-compress-s-c$fix-pp-lst$for-s ((pp1-lst rp-term-listp)
                                               (pp2-lst rp-term-listp)
                                               &key
                                               (pp-flg 't))
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :prepwork ((local
                (in-theory (e/d (measure-lemmas)
                                ((:REWRITE MEASURE-LEMMA1)
                                 (:REWRITE DEFAULT-CAR)
                                 ;;                                 (:REWRITE ACL2::O-P-O-INFP-CAR)
                                 (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                 (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                 (:TYPE-PRESCRIPTION RP-TERMP)
                                 (:TYPE-PRESCRIPTION RP-EQUAL)
                                 (:REWRITE MEASURE-LEMMA1-2)
                                 (:DEFINITION RP-EQUAL))))))
    :returns (mv (res-pp1-lst rp-term-listp
                              :hyp (rp-term-listp pp1-lst))
                 (changed booleanp))
    (b* (((when (or (atom pp1-lst)
                    (atom pp2-lst)))
          (mv pp1-lst nil))
         (c1 (car pp1-lst))
         (c2 (car pp2-lst))
         ((mv new-c1 changed)
          (cond ((rp-equal c1 c2)
                 (case-match c1
                   (('-- n)
                    (mv n t))
                   (&
                    (mv `(-- ,c1) t))))
                (t (mv nil nil))))
         ((when changed)
          (b* (((mv pp1-lst-rest &)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) (cdr
                                                                    pp2-lst) :pp-flg pp-flg )))
            (mv (cons new-c1 pp1-lst-rest) t)))
         ((mv order &)
          (if pp-flg
              (pp-order (ex-from-rp/--loose c1) (ex-from-rp/--loose c2))
            (s-order (ex-from-rp/--loose c1) (ex-from-rp/--loose c2)))))
      (if order
          (b* (((mv pp1-lst-rest rest-changed)
                (ligth-compress-s-c$fix-pp-lst$for-s (cdr pp1-lst) pp2-lst :pp-flg pp-flg )))
            (mv (cons-with-hint c1 pp1-lst-rest pp1-lst) rest-changed))
        (b* (((mv pp1-lst-rest rest-changed)
              (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst (cdr pp2-lst)
                                                   :pp-flg pp-flg )))
          (mv pp1-lst-rest rest-changed)))))

  (define light-compress-s-c$fix-pp$for-s ((pp1 rp-termp)
                                           (pp2 rp-termp)
                                           &key
                                           (pp-flg 't))
    :returns (res-pp1 rp-termp :hyp (rp-termp pp1))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst changed)
          (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst pp2-lst :pp-flg pp-flg)))
      (if changed
          (create-list-instance pp1-lst)
        pp1)))

  (define light-compress-s-c$pass-pp-lst ((pp1-lst rp-term-listp)
                                          (pp2-lst rp-term-listp)
                                          &key
                                          (pp-flg 't))
    :measure (+ (cons-count pp1-lst)
                (cons-count pp2-lst))
    :prepwork ((local
                (in-theory (e/d (measure-lemmas)
                                ((:REWRITE MEASURE-LEMMA1)
                                 (:REWRITE DEFAULT-CAR)
                                 ;;                                 (:REWRITE ACL2::O-P-O-INFP-CAR)
                                 (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                 (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                 (:TYPE-PRESCRIPTION RP-TERMP)
                                 (:TYPE-PRESCRIPTION RP-EQUAL)
                                 (:REWRITE MEASURE-LEMMA1-2)
                                 (:DEFINITION RP-EQUAL))))))
    :returns (mv (res-pp1-lst rp-term-listp
                              :hyp (rp-term-listp pp1-lst))
                 (res-pp2-lst rp-term-listp
                              :hyp (and (rp-term-listp pp1-lst)
                                        (rp-term-listp pp2-lst)))
                 (changed booleanp))
    (b* (((when (or (atom pp1-lst)
                    (atom pp2-lst)))
          (mv pp1-lst pp2-lst nil))
         (c1 (car pp1-lst))
         (c2 (car pp2-lst))
         ((mv c1-abs c1-signed)
          (abs-term c1))
         ;;(case-match c1 (('-- c1) (mv c1 t)) (& (mv c1 nil))))
         ((mv c2-abs c2-signed)
          (abs-term c2))
         ;;(case-match c2 (('-- c2) (mv c2 t)) (& (mv c2 nil))))
         ((mv to-pass passable)
          (cond ((and (rp-equal c1-abs c2-abs)
                      (not (equal c1-signed c2-signed)))
                 (mv c1 t))
                (t (mv nil nil))))
         ((when passable)
          (b* (((mv pp1-lst-rest pp2-lst-rest &)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) (cdr pp2-lst)
                                                :pp-flg pp-flg)))
            (mv pp1-lst-rest (cons to-pass pp2-lst-rest) t)))
         ((mv order &)
          (if pp-flg
              (pp-order (ex-from-rp/--loose c1-abs) (ex-from-rp/--loose
                                                     c2-abs))
            (s-order (ex-from-rp/--loose c1-abs) (ex-from-rp/--loose c2-abs)))))
      (if order
          (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
                (light-compress-s-c$pass-pp-lst (cdr pp1-lst) pp2-lst :pp-flg pp-flg)))
            (mv (cons-with-hint c1 pp1-lst-rest pp1-lst)
                pp2-lst-rest rest-changed))
        (b* (((mv pp1-lst-rest pp2-lst-rest rest-changed)
              (light-compress-s-c$pass-pp-lst pp1-lst (cdr pp2-lst) :pp-flg pp-flg)))
          (mv pp1-lst-rest (cons-with-hint c2 pp2-lst-rest pp2-lst) rest-changed)))))

  (define light-compress-s-c$pass-pp ((pp1 rp-termp)
                                      (pp2 rp-termp)
                                      &key
                                      (pp-flg 't))
    :returns (mv (res-pp1 rp-termp :hyp (rp-termp pp1))
                 (res-pp2 rp-termp :hyp (and (rp-termp pp1)
                                             (rp-termp pp2)))
                 (changed booleanp))
    (b* ((pp1-lst (list-to-lst pp1))
         (pp2-lst (list-to-lst pp2))
         ((mv pp1-lst pp2-lst changed)
          (light-compress-s-c$pass-pp-lst pp1-lst pp2-lst :pp-flg pp-flg)))
      (if changed
          (mv (create-list-instance pp1-lst) (create-list-instance pp2-lst) t)
        (mv pp1 pp2 nil))))

  (local
   (defthmd o<-chain
     (and (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (car x))
                       (cons-count y)))
          (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (cdr x))
                       (cons-count y))))
     :hints (("Goal"
              :in-theory (e/d (cons-count) ())))))

  (local
   (defthmd o<-chain-2
     (and (implies (and
                    (syntaxp (equal (all-vars x)
                                    (all-vars y)))
                    (force (O< (cons-count x) (cons-count y))))
                   (O< (cons-count (ex-from-rp x))
                       (cons-count y))))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               measure-lemmas
;cons-count
                               )
                              ())))))

  (define light-compress-s-c-aux ((pp rp-termp)
                                  (s rp-termp)
                                  (c-arg rp-termp))
    :returns (mv (pp-res rp-termp :hyp (rp-termp pp))
                 (s-res rp-termp :hyp (rp-termp s))
                 (c-arg-res rp-termp :hyp (and (rp-termp pp)
                                               (rp-termp s)
                                               (rp-termp c-arg)))
                 (changed booleanp))
    :measure (cons-count c-arg)
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas
                              o<-chain-2
                              o<-chain)
                             ())))
    :verify-guards :after-returns
    (case-match c-arg
      (('list single-c)
       (b* ((single-c (ex-from-rp$ single-c))
            ((unless (and (single-c-p single-c)))
             (mv pp s c-arg nil))
            (pp-arg1 (cadddr single-c))
            (s-arg1 (caddr single-c))
            (c-arg1 (car (cddddr single-c)))
            ((mv pp-new pp-arg1 changed1)
             (light-compress-s-c$pass-pp pp pp-arg1 :pp-flg t))
            ((mv s-new s-arg1 changed2)
             (light-compress-s-c$pass-pp s s-arg1 :pp-flg nil))
            ((unless (or changed1 changed2))
             (mv pp s c-arg nil))
            ((mv pp-arg1 s-arg1 c-arg1 &)
             (light-compress-s-c-aux pp-arg1 s-arg1 c-arg1)))
         (mv pp-new s-new
             `(list (c ',(calculate-c-hash s-arg1 pp-arg1 c-arg1)
                       ,s-arg1 ,pp-arg1 ,c-arg1))
             t)))
      (& (mv pp s c-arg nil))))

  (define light-compress-s-c ((term rp-termp))
    :prepwork ((local
                (in-theory (enable measure-lemmas))))
    :returns (res-term rp-termp :hyp (rp-termp term))
    (b* ((term-orig term)
         (term (ex-from-rp$ term)))
      (case-match term
        (('s & pp ('list single-c))
         (b* ((single-c (ex-from-rp$ single-c)))
           (case-match single-c
             (('c & & c-pp &)
              (b* ((pp (light-compress-s-c$fix-pp$for-s pp c-pp))
                   ((mv pp s-res c-arg changed)
                    (light-compress-s-c-aux pp ''nil (cadddr term)))
                   ((unless (and changed
                                 (equal s-res ''nil))) ;; this has to be nil
                    ;; all the time but to make the proofs easier...
                    term-orig))
                `(s ',(calculate-s-hash pp c-arg) ,pp ,c-arg)))
             (& term-orig))))
        (('c & s pp c-arg)
         (b* (((mv pp s c-arg changed)
               (light-compress-s-c-aux pp s c-arg)))
           (if changed
               `(c ',(calculate-c-hash s pp c-arg) ,s ,pp ,c-arg)
             term-orig)))
        (& term-orig))))

  ;; (define case-match-|('s & pp ('list single-c))|
  ;;   (term)
  ;;   :inline t
  ;;   "Used by decompress-s-c"
  ;;   (case-match term
  ;;     (('s & pp ('list single-c))
  ;;      (mv pp single-c t))
  ;;     (& (mv ''nil ''nil nil))))

  ;; (define case-match-|('c & ''nil pp ('list single-c))| (term)
  ;;   :inline t
  ;;   "Used by decompress-s-c"
  ;;   (case-match term
  ;;     (('c & ''nil pp ('list single-c))
  ;;      (mv pp single-c t))
  ;;     (& (mv ''nil ''nil nil))))

  ;; (define case-match-|('c & ''nil pp ''nil)| (term)
  ;;   :inline t
  ;;   "Used by decompress-s-c"
  ;;   (case-match term
  ;;     (('c & ''nil pp ''nil)
  ;;      (mv pp t))
  ;;     (& (mv ''nil nil))))

  (define decompress-s-c ((term rp-termp) &key (limit '(expt 2 30)))
    :measure (nfix limit)
    :guard (natp limit)
    :returns (mv (res-term)
                 (coughed-s)
                 (coughed-pp))
    :verify-guards nil
    (b* (((when (zp limit)) (mv term ''nil ''nil))
         (term-orig term)
         (term (ex-from-rp$ term)))
      (case-match term
        (('s & pp ('list single-c))
         (b* (((mv single-c coughed-s coughed-pp)
               (decompress-s-c single-c :limit (1- limit)))
              (- (and (not (equal coughed-s ''nil))
                      (hard-error 'decompress-s-c
                                  "We do not expect decompress-s-c to cough s
    terms to s instances yet... ~%" nil)))
              (pp (pp-sum-merge pp coughed-s));; for proofs...

              (pp (pp-sum-merge pp coughed-pp))
              (pp (s-fix-args pp))
              (c (create-list-instance (list single-c))))
           (mv `(s ',(calculate-s-hash pp c) ,pp ,c)
               ''nil
               ''nil)))
        (('c & s pp ('list single-c))
         (b* (((mv single-c coughed-s coughed-pp)
               (decompress-s-c single-c :limit (1- limit)))
              (pp (pp-sum-merge pp coughed-pp))
              ((mv coughed-pp pp) (c-fix-pp-args pp))
              (s (s-sum-merge s coughed-s))
              ((mv coughed-s s) (c-fix-s-args s))
              (c (create-list-instance (list single-c))))
           (mv `(c ',(calculate-c-hash s pp c) ,s ,pp ,c)
               coughed-s
               coughed-pp)))
        (('c & s pp ''nil)
         (b* (((mv coughed-pp pp) (c-fix-pp-args pp))
              ((mv coughed-s s) (c-fix-s-args s))
              (c ''nil))
           (mv `(c ',(calculate-c-hash s pp c) ,s ,pp ,c)
               coughed-s
               coughed-pp)))
        (& (mv term-orig ''nil ''nil))))
    ///

    (acl2::defret
      rp-termp-of-<fn>
      :hyp (rp-termp term)
      (and (rp-termp res-term)
           (rp-termp coughed-pp)
           (rp-termp coughed-s)))

    (verify-guards decompress-s-c-fn)))

#|(progn
(encapsulate
(((c-pattern1-reduce-enabled) => *))
(local
(defun c-pattern1-reduce-enabled ()
nil)))

(defmacro enable-c-pattern1-reduce (enable)
(if enable
`(defattach c-pattern1-reduce-enabled return-t)
`(defattach c-pattern1-reduce-enabled return-nil)))

(enable-c-pattern1-reduce t))||#

(define c-pattern1-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  ;; This function is called before forming a single-c instance as (c s pp c).
  ;; It might be possible to compress the c instance.
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)))
               (c-res-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst))))
  (cond
   ;;(s-lst (mv s-lst pp-lst c-lst))
   ;;((not (c-pattern1-reduce-enabled)) (mv s-lst pp-lst c-lst))
   (t
    (case-match c-lst
      ((('c & c-s c-pp &))
       (b* (((unless (and (pp-lst-subsetp pp-lst (list-to-lst c-pp))
                          (pp-lst-subsetp s-lst (list-to-lst c-s))))
             (mv s-lst pp-lst c-lst))
            (--pp-lst (negate-lst pp-lst t))
            (--s-lst (negate-lst s-lst t))
            (single-c `(c '0
                          ,(create-list-instance --s-lst)
                          ,(create-list-instance --pp-lst)
                          ,(create-list-instance c-lst)))
            (compressed (light-compress-s-c single-c)))
         (case-match compressed
           (('c & ''nil ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c))
                 ((unless (and valid
                               (equal max 0)
                               (equal min -1)))
                  (mv s-lst pp-lst c-lst))
                 ((mv decompressed coughed-s coughed-pp)
                  (decompress-s-c single-c))
                 (coughed-pp-lst (pp-sum-merge-aux pp-lst (list-to-lst
                                                           coughed-pp)))
                 (coughed-s-lst (s-sum-merge-aux s-lst (list-to-lst
                                                        coughed-s)))
                 ((unless (and (equal coughed-pp-lst nil)
                               (equal coughed-s-lst nil)))
                  (mv s-lst pp-lst c-lst)))
              (case-match decompressed
                (('c & s pp ('list . c-lst)) ;; changed it to this way to prove
                 ;; measure of c-sum-merge with count-c.
                 (mv (list-to-lst s) (list-to-lst pp) c-lst))
                (('c & s pp ''nil)
                 (mv (list-to-lst s) (list-to-lst pp) nil))
                (& (mv s-lst pp-lst c-lst)))))
           (& (mv s-lst pp-lst c-lst)))))
      (& (mv s-lst pp-lst c-lst))))))

#|(local
(defthmd and-subsetp-IMPLIES-and-list-intance
(implies (and-subsetp pp1 pp2)
(B* ((PP1 (EX-FROM-RP$ PP1))
(PP2 (EX-FROM-RP$ PP2)))
(AND (CASE-MATCH PP1 (('AND-LIST & ('LIST . &)) T))
(CASE-MATCH PP2 (('AND-LIST & ('LIST . &)) T)))))
:rule-classes :forward-chaining
:hints (("Goal"
:in-theory (e/d (and-subsetp) ())))))|#

(progn
  (define and-list-instance-to-binary-and-aux ((lst))
    :returns (res rp-termp
                  :hyp (rp-term-listp lst))
    (if (atom lst)
        ''1
      `(binary-and ,(car lst)
                   ,(and-list-instance-to-binary-and-aux (cdr lst)))))

  (define and-list-instance-to-binary-and ((term))
    :Returns (res rp-termp
                  :hyp (rp-termp term))
    (case-match term
      (('and-list & ('list . lst))
       (and-list-instance-to-binary-and-aux lst))
      (& term))))

(define single-s-to-pp-lst ((pp1 rp-termp)
                            (pp2 rp-termp)
                            (pp3 rp-termp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-termp pp1)
                                     (rp-termp pp2)
                                     (rp-termp pp3)))
               (success booleanp))
  :verify-guards nil
  (b* ((pp1 (and-list-instance-to-binary-and pp1))
       (pp2 (and-list-instance-to-binary-and pp2))
       (pp3 (and-list-instance-to-binary-and pp3))
       ((Unless (and (pp-term-p pp1)
                     (pp-term-p pp2)
                     (pp-term-p pp3)
                     ))
        (mv nil nil)))
    (mv (pp-flatten `(binary-xor ,pp1
                                 (binary-xor ,pp2
                                             ,pp3))
                    nil)
        t))
  ///
  (verify-guards single-s-to-pp-lst
    :hints (("Goal"
             :expand ((:free (x y)
                             (pp-term-p `(binary-xor ,x ,y))))
             :in-theory (e/d (is-rp ex-from-rp) ())))))

(define single-c-to-pp-lst ((pp1 rp-termp)
                            (pp2 rp-termp)
                            (pp3 rp-termp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-termp pp1)
                                     (rp-termp pp2)
                                     (rp-termp pp3)))
               (success booleanp))
  :verify-guards nil
  (b* ((pp1 (and-list-instance-to-binary-and pp1))
       (pp2 (and-list-instance-to-binary-and pp2))
       (pp3 (and-list-instance-to-binary-and pp3))
       ((Unless (and (pp-term-p pp1)
                     (pp-term-p pp2)
                     (pp-term-p pp3)))
        (mv nil nil)))
    (mv (pp-flatten `(binary-or (binary-and ,pp1 ,pp2)
                                (binary-or (binary-and ,pp2 ,pp3)
                                           (binary-and ,pp1 ,pp3)))
                    nil)
        t))
  ///
  (verify-guards single-c-to-pp-lst
    :hints (("Goal"
             :expand ((:free (x y)
                             (pp-term-p `(binary-or ,x ,y))))
             :in-theory (e/d (is-rp ex-from-rp) ())))))

(progn
  (encapsulate
    (((pattern2-reduce-enabled) => *))
    (local
     (defun pattern2-reduce-enabled ()
       nil)))

  (defmacro enable-pattern2-reduce (enable)
    (if enable
        `(defattach  pattern2-reduce-enabled return-t)
      `(defattach  pattern2-reduce-enabled return-nil)))

  (enable-pattern2-reduce t))

#|(progn
(encapsulate
(((pattern2-aggressive-reduce-enabled) => *))
(local
(defun pattern2-aggressive-reduce-enabled ()
nil)))

(defmacro enable-pattern2-aggressive-reduce  (enable)
(if enable
`(defattach pattern2-aggressive-reduce-enabled return-t)
`(defattach pattern2-aggressive-reduce-enabled return-nil)))

(enable-pattern2-aggressive-reduce nil))||#

(define has-unflatenned-pp ((pp-lst rp-term-listp))
  (if (atom pp-lst)
      nil
    (or (binary-fnc-p (ex-from-rp$ (car pp-lst)))
        (has-unflatenned-pp (cdr pp-lst)))))

(define c-pattern2-reduce-aux-cond (new-pp-lst)
  (and (consp new-pp-lst)
       (not (cdr new-pp-lst))
       (let ((e (car new-pp-lst)))
         (case-match e
           (('and-list & ('list . lst))
            (<= (len lst) 4)
            )))))

(define c-pattern2-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  :returns (mv
            (res-pp-lst rp-term-listp
                        :hyp (rp-term-listp pp-lst))
            (reducedp booleanp))

  :verify-guards :after-returns
  (b* (((unless (and (not s-lst)
                     (not c-lst)
                     (not (has-unflatenned-pp pp-lst))
                     (pattern2-reduce-enabled)))
        (mv nil nil))

       ;;(aggressive (pattern2-aggressive-reduce-enabled))
       )
    (case-match pp-lst
      ((''1 pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst1 success1) (single-c-to-pp-lst pp1 pp2 pp3))
            ((mv new-pp-lst2 success2) (single-s-to-pp-lst pp1 pp2 pp3))
            ((unless (and success1 success2))
             (mv nil nil)))
         (mv (pp-sum-merge-aux new-pp-lst1 new-pp-lst2)  t)))
      ((pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success) (single-c-to-pp-lst pp1 pp2 pp3))
            ((unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ((pp1 pp2)
       (b* (((mv new-pp-lst success) (single-c-to-pp-lst pp1 pp2 ''0)))
         (if (and success
                  (or t
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1))
                      (c-pattern2-reduce-aux-cond new-pp-lst)))
             (mv new-pp-lst t)
           (mv nil nil))))
      (& (mv nil nil)))))

(define pattern0-syntax-check ((s-lst rp-term-listp)
                               (pp-lst rp-term-listp)
                               (c-lst rp-term-listp)
                               (limit natp))
  :returns (valid-syntax booleanp)
  :measure (nfix limit)
  (b* (((when (zp limit)) nil)
       ((mv pp-cnt pp-valid) (case-match pp-lst
                               ((& &) (mv 2 t))
                               ((&) (mv 1 t))
                               (() (mv 0 t))
                               (& (mv 0 nil))))
       ((unless pp-valid) nil)
       (total-cnt pp-cnt)
       ((mv s-cnt s-valid)
        (case-match s-lst
          (()
           (mv 0 t))
          ((x)
           (mv 1 (b* (((when (> (1+ total-cnt) 2)) nil)
                      (x (ex-from-rp x)))
                   (case-match x
                     (('s & pp-arg c-arg)
                      (pattern0-syntax-check nil
                                             (list-to-lst pp-arg)
                                             (list-to-lst c-arg)
                                             (1- limit)))))))
          ((x y)
           (mv 2 (b* (((when (> (+ 2 total-cnt) 2)) nil)
                      (x (ex-from-rp x))
                      (y (ex-from-rp y)))
                   (and
                    (case-match x
                      (('s & pp-arg c-arg)
                       (pattern0-syntax-check nil
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))
                    (case-match y
                      (('s & pp-arg c-arg)
                       (pattern0-syntax-check nil
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))))))
          (& (mv 0 nil))))
       ((Unless s-valid) nil)
       (total-cnt (+ pp-cnt s-cnt))
       ((mv c-cnt c-valid)
        (case-match c-lst
          (()
           (mv 0 t))
          ((x)
           (mv 1 (b* (((when (> (1+ total-cnt) 2)) nil)
                      (x (ex-from-rp x)))
                   (case-match x
                     (('c & s-arg pp-arg c-arg)
                      (pattern0-syntax-check (list-to-lst s-arg)
                                             (list-to-lst pp-arg)
                                             (list-to-lst c-arg)
                                             (1- limit)))))))
          ((x y)
           (mv 2 (b* (((when (> (+ 2 total-cnt) 2)) nil)
                      (x (ex-from-rp x))
                      (y (ex-from-rp y)))
                   (and
                    (case-match x
                      (('c & s-arg pp-arg c-arg)
                       (pattern0-syntax-check (list-to-lst s-arg)
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))
                    (case-match y
                      (('c & s-arg pp-arg c-arg)
                       (pattern0-syntax-check (list-to-lst s-arg)
                                              (list-to-lst pp-arg)
                                              (list-to-lst c-arg)
                                              (1- limit))))))))
          (& (mv 0 nil))))
       ((unless c-valid) nil))
    (= (+ s-cnt c-cnt pp-cnt) 2)))

;; (or (and (case-match pp-lst
;;            ((& &) t))
;;          (atom c-lst)
;;          (atom s-lst))
;;     (and (case-match pp-lst
;;            ((&) t))
;;          (or (case-match c-lst
;;                ((x)
;;                 (b* ((x (ex-from-rp x)))
;;                   (case-match x
;;                     (('c & s-arg pp-arg c-arg)
;;                      (pattern0-syntax-check (list-to-lst s-arg)
;;                                             (list-to-lst pp-arg)
;;                                             (list-to-lst c-arg)))))))
;;              (case-match s-lst
;;                ((x)
;;                 (b* ((x (ex-from-rp x)))
;;                   (case-match x
;;                     (('s & s-arg pp-arg c-arg)
;;                      (pattern0-syntax-check (list-to-lst s-arg)
;;                                             (list-to-lst pp-arg)
;;                                             (list-to-lst c-arg)))))))))
;;     (and (atom pp-lst)
;;          (case-match c-lst
;;            ((x y)
;;             (b* ((x (ex-from-rp x))
;;                  (y (ex-from-rp y)))
;;               (and
;;                (case-match x
;;                  (('c & s-arg pp-arg c-arg)
;;                   (pattern0-syntax-check (list-to-lst s-arg)
;;                                          (list-to-lst pp-arg)
;;                                          (list-to-lst c-arg))))
;;                (case-match y
;;                  (('c & s-arg pp-arg c-arg)
;;                   (pattern0-syntax-check (list-to-lst s-arg)
;;                                          (list-to-lst pp-arg)
;;                                          (list-to-lst c-arg)))))))))))

(define pattern0-reduce-aux-pp-lst ((pp-lst rp-term-listp))
  :returns (mv (pp1 rp-termp :hyp (rp-term-listp pp-lst))
               (pp2 rp-termp :hyp (rp-term-listp pp-lst))
               (pp-cnt natp)
               (pp-valid booleanp))
  (case-match pp-lst
    ((pp1 pp2)
     (if (and (pp-term-p pp1)
              (pp-term-p pp2))
         (mv pp1 pp2 2 t)
       (mv ''nil ''nil 0 nil)))
    ((pp1)
     (if (pp-term-p pp1)
         (mv pp1 ''0 1 t)
       (mv ''nil ''nil 0 nil)))
    (()
     (mv ''0 ''0 0 t))
    (&
     (mv ''nil ''nil 0 nil)))
  ///

  (defret pp-term-p-<fn>
    (implies pp-valid
             (and (pp-term-p pp1)
                  (pp-term-p pp2)))))

(acl2::defines
  pattern0-reduce-aux

  :flag-defthm-macro defthm-pattern0-reduce-aux
  :flag-local nil

  :returns-hints (("Goal"
                   :expand ((PATTERN0-REDUCE-AUX NIL PP-LST NIL LIMIT))
                   :do-not-induct t
                   :in-theory (e/d () ())))

  :prepwork ((local
              (in-theory (disable (:DEFINITION NOT)
                                  (:DEFINITION NATP)

                                  (:REWRITE ACL2::ZP-OPEN)
                                  (:TYPE-PRESCRIPTION SINGLE-C-P$INLINE)
                                  (:TYPE-PRESCRIPTION RP-TERMP)
                                  (:TYPE-PRESCRIPTION ACL2::ELEMENT-LIST-P)
                                  (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP)
                                  ;;(:TYPE-PRESCRIPTION SINGLE-S-P$INLINE)
                                  ;;(:DEFINITION QUOTEP)
                                  (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                                  (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                  ;;(:REWRITE RP-TERMP-CAR-CDDDDR)

                                  (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                  (:REWRITE DEFAULT-+-1)

                                  (:TYPE-PRESCRIPTION PP-TERM-P-fn)

                                  ;;                                 (:REWRITE ACL2::O-INFP->NEQ-0)

                                  (:REWRITE ACL2::FOLD-CONSTS-IN-+)
                                  (:TYPE-PRESCRIPTION O-FINP)

                                  (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                  (:DEFINITION PP-TERM-P-fn)
                                  (:REWRITE DEFAULT-CDR)
                                  (:REWRITE DEFAULT-CAR)
                                  (:REWRITE DEFAULT-+-2)
                                  (:REWRITE IS-IF-RP-TERMP)
                                  (:REWRITE IS-RP-PSEUDO-TERMP)

                                  ))))

  :verify-guards nil

  (define pattern0-reduce-aux-s-lst ((s-lst rp-term-listp)
                                     (limit natp)
                                     (search-limit integerp))
    :returns (mv (s1 rp-termp :hyp (rp-term-listp s-lst))
                 (s2 rp-termp :hyp (rp-term-listp s-lst))
                 (s-cnt natp)
                 (s-valid booleanp))
    :measure (nfix limit)
    (if (zp limit)
        (mv ''nil ''nil 0 nil)
      (case-match s-lst
        ((s1 s2)
         (b* (((when (< (- search-limit 2) 0))
               (mv ''nil ''nil 0 nil))
              (s1 (ex-from-rp s1))
              (s2 (ex-from-rp s2))
              ((unless (and (single-s-p s1)
                            (single-s-p s2)))
               (mv ''nil ''nil 0 nil))
              ((mv term1 term2 s1-valid)
               (pattern0-reduce-aux nil
                                    (list-to-lst (caddr s1))
                                    (list-to-lst (cadddr s1))
                                    (1- limit)))
              ((unless s1-valid)
               (mv ''nil ''nil 0 nil))
              (s1 `(binary-xor ,term1 ,term2))
              ((mv term1 term2 s2-valid)
               (pattern0-reduce-aux nil
                                    (list-to-lst (caddr s2))
                                    (list-to-lst (cadddr s2))
                                    (1- limit)))
              ((unless s2-valid)
               (mv ''nil ''nil 0 nil))
              (s2 `(binary-xor ,term1 ,term2)))
           (mv s1 s2 2 t)))
        ((s1)
         (b* (((when (< (- search-limit 1) 0))
               (mv ''nil ''nil 0 nil))
              (s1 (ex-from-rp s1))
              ((unless (single-s-p s1))
               (mv ''nil ''nil 0 nil))
              ((mv term1 term2 s1-valid)
               (pattern0-reduce-aux nil
                                    (list-to-lst (caddr s1))
                                    (list-to-lst (cadddr s1))
                                    (1- limit)))
              ((unless s1-valid)
               (mv ''nil ''nil 0 nil))
              (s1 `(binary-xor ,term1 ,term2)))
           (mv s1 ''0 1 t)))
        (()
         (mv ''0 ''0 0 t))
        (&
         (mv ''nil ''nil 0 nil)))))

  (define pattern0-reduce-aux-c-lst ((c-lst rp-term-listp)
                                     (limit natp)
                                     (search-limit integerp))
    :returns (mv (c1 rp-termp :hyp (rp-term-listp c-lst))
                 (c2 rp-termp :hyp (rp-term-listp c-lst))
                 (c-cnt natp)
                 (c-valid booleanp))
    :measure (nfix limit)
    (if (zp limit)
        (mv ''nil ''nil 0 nil)
      (case-match c-lst
        ((c1 c2)
         (b* (((when (< (- search-limit 2) 0))
               (mv ''nil ''nil 0 nil))
              (c1 (ex-from-rp c1))
              (c2 (ex-from-rp c2))
              ((unless (and (single-c-p c1)
                            (single-c-p c2)))
               (mv ''nil ''nil 0 nil))
              ((mv term1 term2 c1-valid)
               (pattern0-reduce-aux (list-to-lst (caddr c1))
                                    (list-to-lst (cadddr c1))
                                    (list-to-lst (caddr(cddr c1)))
                                    (1- limit)))
              ((unless c1-valid)
               (mv ''nil ''nil 0 nil))
              (c1 `(binary-and ,term1 ,term2))
              ((mv term1 term2 c2-valid)
               (pattern0-reduce-aux (list-to-lst (caddr c2))
                                    (list-to-lst (cadddr c2))
                                    (list-to-lst (caddr(cddr c2)))
                                    (1- limit)))
              ((unless c2-valid)
               (mv ''nil ''nil 0 nil))
              (c2 `(binary-and ,term1 ,term2)))
           (mv c1 c2 2 t)))
        ((c1)
         (b* (((when (< (- search-limit 1) 0))
               (mv ''nil ''nil 0 nil))
              (c1 (ex-from-rp c1))
              ((unless (single-c-p c1))
               (mv ''nil ''nil 0 nil))
              ((mv term1 term2 c1-valid)
               (pattern0-reduce-aux (list-to-lst (caddr c1))
                                    (list-to-lst (cadddr c1))
                                    (list-to-lst (caddr(cddr c1)))

                                    (1- limit)))
              ((unless c1-valid)
               (mv ''nil ''nil 0 nil))
              (c1 `(binary-and ,term1 ,term2)))
           (mv c1 ''0 1 t)))
        (()
         (mv ''0 ''0 0 t))
        (&
         (mv ''nil ''nil 0 nil)))))

  (define pattern0-reduce-aux ((s-lst rp-term-listp)
                               (pp-lst rp-term-listp)
                               (c-lst rp-term-listp)
                               (limit natp))
    :returns (mv (pp-term1 rp-termp :hyp (and (rp-term-listp s-lst)
                                              (rp-term-listp pp-lst)
                                              (rp-term-listp c-lst)))
                 (pp-term2 rp-termp :hyp (and (rp-term-listp s-lst)
                                              (rp-term-listp pp-lst)
                                              (rp-term-listp c-lst)))
                 (valid booleanp))
    :measure (nfix limit)

    ;;:verify-guards nil

    (b* (((when (zp limit)) (mv ''nil ''nil nil))
         ((mv pp1 pp2 pp-cnt pp-valid)
          (pattern0-reduce-aux-pp-lst pp-lst))
         ((unless pp-valid)
          (mv ''nil ''nil nil))
         ((mv s1 s2 s-cnt s-valid)
          (pattern0-reduce-aux-s-lst s-lst (1- limit) (- 2 pp-cnt)))
         ((unless s-valid)
          (mv ''nil ''nil nil))
         ((mv c1 c2 c-cnt c-valid)
          (pattern0-reduce-aux-c-lst c-lst (1- limit) (+ 2 (- pp-cnt) (- s-cnt))))
         ((unless c-valid)
          (mv ''nil ''nil nil)))
      (cond ((and* (= s-cnt 0) (= pp-cnt 0) (= c-cnt 2))
             (mv c1 c2 t))
            ((and* (= s-cnt 0) (= pp-cnt 1) (= c-cnt 1))
             (mv pp1 c1 t))
            ((and* (= s-cnt 0) (= pp-cnt 2) (= c-cnt 0))
             (mv pp1 pp2 t))
            ((and* (= s-cnt 1) (= pp-cnt 0) (= c-cnt 1))
             (mv s1 c1 t))
            ((and* (= s-cnt 1) (= pp-cnt 1) (= c-cnt 0))
             (mv s1 pp1 t))
            ((and* (= s-cnt 2) (= pp-cnt 0) (= c-cnt 0))
             (mv s1 s2 t))
            (t
             (mv ''nil ''nil nil)))))
  ///

  (local
   (defthm dummy-lemma
     (and (implies (and (natp x)
                        (natp y))
                   (and (integerp (+ 2 (- x) (- y)))))
          (implies (natp x)
                   (integerp (+ 2 (- x)))))))

  (verify-guards  pattern0-reduce-aux
    :hints (("Goal"
             :in-theory (e/d ()
                             ((:TYPE-PRESCRIPTION SINGLE-S-P$INLINE)
                              (:TYPE-PRESCRIPTION SINGLE-c-P$INLINE)
                              (:TYPE-PRESCRIPTION O<)
                              (:TYPE-PRESCRIPTION ZP)
                              (:TYPE-PRESCRIPTION QUOTEP)
                              (:REWRITE RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                              (:REWRITE EXTRACT-FROM-RP-PSEUDO-TERM-LISTP)
                              (:REWRITE LOCAL-MEASURE-LEMMA4)
                              (:REWRITE RP-TERMP-CADDDDR)
                              ;;(:DEFINITION QUOTEP)
                              (:REWRITE RP-TERMP-CADR)
                              (:REWRITE RP-TERMP-EXTRACT-FROM-RP)
                              (:FORWARD-CHAINING DUMMMY-RP-TERM-LISTP-LEMMA)
                              (:REWRITE DUMMY-RP-TERM-LISTP-LEMMA))))))

  (defret-mutual pp-term-p-of-<fn>
    (defret pp-term-p-of-<fn>
      (implies s-valid
               (and (pp-term-p s1)
                    (pp-term-p s2)))
      :fn pattern0-reduce-aux-s-lst)
    (defret pp-term-p-of-<fn>
      (implies c-valid
               (and (pp-term-p c1)
                    (pp-term-p c2)))
      :fn pattern0-reduce-aux-c-lst)
    (defret pp-term-p-of-<fn>
      (implies valid
               (and (pp-term-p pp-term1)
                    (pp-term-p pp-term2)))
      :fn pattern0-reduce-aux)
    :hints (("Goal"
             :expand ((PATTERN0-REDUCE-AUX NIL PP-LST NIL LIMIT)
                      (:free (x) (pp-term-p (cons 'binary-and x)))
                      (:free (x) (pp-term-p (cons 'binary-xor x)))
                      (:free (x) (ex-from-rp (cons 'binary-and x)))
                      (:free (x) (ex-from-rp (cons 'binary-xor x))))
             :do-not-induct t
             :in-theory (e/d (is-rp) ()))))

  )

;;     ((when (and (case-match pp-lst
;;                  ((& &) t))
;;                (atom c-lst)))
;;     (if (and (pp-term-p (car pp-lst))
;;              (pp-term-p (cadr pp-lst)))
;;         (mv `(,binary-fnc ,(car pp-lst) ,(cadr pp-lst)) t)
;;       (mv ''nil nil)))
;;    ((when (and (case-match pp-lst
;;                  ((&) t))
;;                (case-match c-lst
;;                  ((c1)
;;                   (b* ((c1 (ex-from-rp c1))) (single-c-p c1))))))
;;     (b* ((c1 (ex-from-rp (car c-lst)))
;;          (s-arg-lst (list-to-lst (caddr c1)))
;;          (pp-arg-lst (list-to-lst (cadddr c1)))
;;          (c-arg-lst (list-to-lst (caddr(cddr c1))))
;;          ((mv pp-term1 valid)
;;           (pattern0-reduce-aux s-arg-lst pp-arg-lst c-arg-lst 'binary-and))
;;          ((unless valid) (mv ''nil nil))
;;          ((unless (pp-term-p (car pp-lst))) (mv ''nil nil)))
;;       (mv `(,binary-fnc ,pp-term1 ,(car pp-lst)) t)))
;;    ((when (and (case-match pp-lst
;;                  ((&) t))
;;                (case-match c-lst
;;                  ((c1 c2)
;;                   (and (b* ((c1 (ex-from-rp c1))) (single-c-p c1))
;;                        (b* ((c2 (ex-from-rp c2))) (single-c-p c2)))))))
;;     (b* ((c1 (ex-from-rp (car c-lst)))
;;          (s-arg-lst (list-to-lst (caddr c1)))
;;          (pp-arg-lst (list-to-lst (cadddr c1)))
;;          (c-arg-lst  (list-to-lst (caddr(cddr c1))))
;;          ((mv pp-term1 valid)
;;           (pattern0-reduce-aux s-arg-lst pp-arg-lst c-arg-lst 'binary-and))
;;          ((unless valid) (mv ''nil nil))
;;          (c2 (ex-from-rp (cadr c-lst)))
;;          (s-arg-lst (list-to-lst (caddr c2)))
;;          (pp-arg-lst (list-to-lst (cadddr c2)))
;;          (c-arg-lst (list-to-lst (caddr(cddr c2))))
;;          ((mv pp-term2 valid)
;;           ( pattern0-reduce-aux s-arg-lst pp-arg-lst c-arg-lst 'binary-and))
;;          ((unless valid) (mv ''nil nil)))
;;       (mv `(,binary-fnc ,pp-term1 ,pp-term2) t))))
;; (mv ''nil nil)))

(define c-pattern0-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp))
  :returns (reduced booleanp)
  :verify-guards t
  :guard-hints (("Goal"
                 :expand ((:free (x) (pp-term-p (cons 'binary-and x)))
                          (:free (x) (ex-from-rp (cons 'binary-and x))))
                 :in-theory (e/d (is-rp) (pp-term-p))))

  (and (pattern0-syntax-check s-lst pp-lst c-lst 10)
       (b* (((when (or (cons-count-compare pp-lst 50)
                       (cons-count-compare s-lst 100)
                       (cons-count-compare c-lst 150)))
             nil)
            ((mv pp-term1 pp-term2 valid)
             (pattern0-reduce-aux s-lst pp-lst c-lst 10))
            ((unless valid) nil)
            (flatten-res (pp-flatten `(binary-and ,pp-term1 ,pp-term2) nil))
            ((when (not flatten-res))
             (progn$ (cw "c-pattern0-reduce match (3)! ~%")
                     #|(cw "s-lst: ~p0, pp-lst: ~p1, c-lst: ~p2 ~%"
                     s-lst pp-lst c-lst)||#
                     t)))
         nil
         ))

  #|(b* (

  ;; ((when (and nil
  ;;             (not s-lst)
  ;;             (consp pp-lst)
  ;;             (consp (cdr pp-lst))
  ;;             (not (cddr pp-lst))
  ;;             (not c-lst)))
  ;;  (b* ((pp-arg1 (car pp-lst))
  ;;       (pp-arg2 (cadr pp-lst))
  ;;       ((Unless (and (pp-term-p pp-arg1)
  ;;                     (pp-term-p pp-arg2)
  ;;                     ))
  ;;        nil)
  ;;       (flatten-res (pp-flatten
  ;;                     `(binary-and ,pp-arg1 ,pp-arg2)
  ;;                     nil
  ;;                     :unpack-now t))
  ;;       (& (cw "flatten-res ~p0 ~%" flatten-res))
  ;;       ((when (not flatten-res))
  ;;        (progn$ (and (pattern0-syntax-check s-lst pp-lst c-lst)
  ;;                     (cw "c-pattern0-syntax match"))
  ;;                (cw "c-pattern0-reduce match (1)! ~%")
  ;;                t)))
  ;;    nil))
  ;; ((when (and nil
  ;;             (not s-lst)
  ;;             (consp pp-lst)
  ;;             (not (cdr pp-lst))
  ;;             (consp c-lst)
  ;;             (not (cdr c-lst))
  ;;             (b* ((single-c-arg (ex-from-rp (car c-lst)))
  ;;                  ((unless (single-c-p single-c-arg)) nil)
  ;;                  (pp-args (list-to-lst (cadddr single-c-arg))))
  ;;               (and (consp pp-args)
  ;;                    (consp (cdr pp-args))
  ;;                    (not (cddr pp-args))
  ;;                    (equal (caddr single-c-arg) ''nil)
  ;;                    (equal (caddr (cddr single-c-arg)) ''nil)))))
  ;;  (b* ((pp-arg1 (car pp-lst))
  ;;       (single-c-arg (ex-from-rp (car c-lst)))
  ;;       (inner-pp-args (list-to-lst (cadddr single-c-arg)))
  ;;       (pp-arg2 (car inner-pp-args))
  ;;       (pp-arg3 (cadr inner-pp-args))
  ;;       ((Unless (and (pp-term-p pp-arg1)
  ;;                     (pp-term-p pp-arg2)
  ;;                     (pp-term-p pp-arg3)))
  ;;        nil)
  ;;       (flatten-res (pp-flatten
  ;;                     `(binary-and
  ;;                       ,pp-arg1
  ;;                       (binary-and ,pp-arg2 ,pp-arg3))
  ;;                     nil
  ;;                     :unpack-now t))
  ;;       (& (cw "flatten-res ~p0 ~%" flatten-res))
  ;;       ((when (not flatten-res))
  ;;        (progn$ (if (pattern0-syntax-check s-lst pp-lst c-lst)
  ;;                    (cw "c-pattern0-syntax match ")
  ;;                  (cw "s-lst: ~p0, pp-lst:~p1, c-lst:~p2 ~%" s-lst pp-lst c-lst))
  ;;                (cw "c-pattern0-reduce match (2)! ~%")
  ;;                t)))
  ;;    nil))
  ((when (pattern0-syntax-check s-lst pp-lst c-lst))
  (b* (((mv pp-term valid)
  (pattern0-reduce-aux s-lst pp-lst c-lst 'binary-and))
  ((unless valid) (or (cw "c-pattern0-reduce match somehow invalid(3) ~%" s-lst pp-lst c-lst) t))
  (flatten-res (pp-flatten pp-term nil :unpack-now t))
  ((when (not flatten-res))
  (progn$ (cw "c-pattern0-reduce match (3)! ~%")
  ;;(cw "s-lst:~p0 pp-lst:~p1 c-lst:~p2  ~%" s-lst pp-lst c-lst)
  t)))
  nil;;(cw "c-pattern0-reduce match missed (3)! ~%")
  )))
  (and (pattern0-syntax-check s-lst pp-lst c-lst)
  (cw "c-pattern0 missed a case ~%")))||#
  ///
  (verify-guards c-pattern0-reduce
    :hints (("Goal"
             :expand ((:free (x)
                             (pp-term-p (cons 'binary-and x)))
                      (:free (x)
                             (ex-from-rp (cons 'binary-and x))))
             :in-theory (e/d (is-rp) ())))))

(define s-pattern0-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (reduced booleanp)
  :verify-guards nil

  (b* ((pp-lst (list-to-lst pp))
       (c-lst (list-to-lst c)))
    (if (pattern0-syntax-check nil pp-lst c-lst 10)
        (b* (((when (or (cons-count-compare pp-lst 50)
                        (cons-count-compare c-lst 150)))
              nil)
             ((mv pp-term1 pp-term2 valid)
              (pattern0-reduce-aux nil pp-lst c-lst 10))
             ((unless valid) nil)
             (flatten-res (pp-flatten `(binary-xor ,pp-term1 ,pp-term2) nil))
             ((when (not flatten-res))
              (progn$ (cw "s-pattern0-reduce match (1,2,3)! ~%")
                      ;;(cw "s-lst:~p0 pp-lst:~p1 c-lst:~p2  ~%" s-lst pp-lst c-lst)
                      t)))
          nil
          #|(cw "s-pattern0-reduce match missed! ~%")||#)
      nil))
  ///
  (verify-guards s-pattern0-reduce
    :hints (("Goal"
             :expand ((:free (x)
                             (pp-term-p (cons 'binary-xor x)))
                      (:free (x)
                             (ex-from-rp (cons 'binary-xor x))))
             :in-theory (e/d (is-rp) ())))))

(defun quoted-listp (lst)
  (declare (xargs :mode :logic :guard t))
  (if (atom lst)
      (EQUAL LST NIL)
    (and (quotep (car lst))
         (consp (cdar lst))
         (quoteD-listp (cdr lst)))))

(define all-quoted-list (term)
  (case-match term
    (('list . lst)
     (quoted-listp lst))
    (''nil
     t)))

#|(define s-pattern3-success ()
t)||#

#|(profile 's-pattern3-success)||#

(progn
  (define light-s-of-s-fix-lst ((s-lst rp-term-listp)
                                (c-lst rp-term-listp))
    :returns (mv (pp-res-lst rp-term-listp
                             :hyp (and (rp-term-listp s-lst)
                                       (rp-term-listp c-lst)))
                 (c-res-lst rp-term-listp
                            :hyp (and (rp-term-listp s-lst)
                                      (rp-term-listp c-lst))))
    ;; similar to s-of-s-fix-lst but it doesn't try to merge c-lsts
    :measure (acl2-count  s-lst)
    (b* (((when (atom s-lst)) (mv nil c-lst))
         ((mv pp-lst c-lst) (light-s-of-s-fix-lst (cdr s-lst) c-lst))
         (cur-s (ex-from-rp/-- (car s-lst))))
      (case-match cur-s
        (('s & cur-pp cur-c)
         (b* ((cur-c-lst (list-to-lst cur-c))
              (c-lst (s-sum-merge-aux c-lst cur-c-lst)) ;; put c's together
              ;; without trying to merge them..
              (pp-lst (pp-sum-merge-aux (list-to-lst cur-pp) pp-lst)))
           (mv pp-lst c-lst)))
        (''nil
         (mv pp-lst c-lst))
        (&
         (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                 (hard-error 's-of-s-fix-aux "Read above.." nil)
                 (mv (cons cur-s pp-lst)
                     c-lst))))))

  (define light-s-of-s-fix ((s rp-termp)
                            (pp rp-termp)
                            (c-lst rp-term-listp))
    :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                            (rp-termp pp)
                                            (rp-term-listp c-lst)))
                 (c-res-lst rp-term-listp :hyp (and (rp-termp s)
                                                    (rp-termp pp)
                                                    (rp-term-listp c-lst))))
    (b* ((s-lst (list-to-lst s))
         ((when (equal s-lst nil))  (mv pp c-lst))
         ((mv pp-lst c-lst)
          (light-s-of-s-fix-lst s-lst c-lst))
         (pp-lst (pp-sum-merge-aux (list-to-lst pp) pp-lst))
         (pp (create-list-instance pp-lst)))
      (mv pp c-lst)))

  (define single-c-try-merge-params-aux-failed ()
    :enabled t
    nil)

  (profile 'single-c-try-merge-params-aux-failed)

  (define single-c-try-merge-params-aux ((cur-s rp-termp)
                                         c-hash-code
                                         (s-arg rp-termp)
                                         (pp-arg rp-termp)
                                         (c-arg-lst rp-term-listp))
    :inline t
    :returns (success booleanp)
    (b* ((cur-s (ex-from-rp$ cur-s)))
      (case-match cur-s
        (('s ('quote s-hash-code) cur-pp-arg cur-c-arg)
         (and (equal c-hash-code s-hash-code)
              (b* (((mv pp-arg c-arg-lst)
                    (light-s-of-s-fix s-arg pp-arg c-arg-lst)))
                (or
                 (and (rp-equal-cnt-subterms c-arg-lst (list-to-lst cur-c-arg) 0)
                      (rp-equal-cnt pp-arg cur-pp-arg 0))
                 ;;(single-c-try-merge-params-aux-failed)
                 ))))
        (&
         (hard-error 'single-c-try-merge-params-aux
                     "Bad form for current s:~p0~%"
                     (list (cons #\0 cur-s)))))))

  (define single-c-try-merge-params ((s-lst rp-term-listp)
                                     c-hash-code
                                     (s-arg rp-termp)
                                     (pp-arg rp-termp)
                                     (c-arg-lst rp-term-listp))
    :returns (mv (updated-s-lst rp-term-listp :hyp (and (rp-term-listp s-lst)))
                 (success booleanp))
    :measure (acl2-count s-lst)

    (b* (((when (atom s-lst))
          (mv s-lst nil))
         ((when (single-c-try-merge-params-aux (car s-lst) c-hash-code
                                               s-arg pp-arg c-arg-lst))
          (mv (cdr s-lst) t))
         ((mv rest-s-lst success)
          (single-c-try-merge-params (cdr s-lst) c-hash-code s-arg pp-arg
                                     c-arg-lst))
         ((when success)
          (mv (cons (car s-lst) rest-s-lst) t)))
      (mv s-lst nil))))

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(progn
  (encapsulate
    (((s-pattern1-reduce-enabled) => *))
    (local
     (defun s-pattern1-reduce-enabled ()
       nil)))

  (defmacro enable-s-pattern1-reduce (enable)
    (if enable
        `(defattach  s-pattern1-reduce-enabled return-t)
      `(defattach  s-pattern1-reduce-enabled return-nil)))

  (enable-s-pattern1-reduce t))

(define s-pattern1-reduce ((pp rp-termp)
                           (c rp-termp))
  ;; :returns (mv pp c reduced reducedp)
  ;; Search for (s pp1 (c pp1 rest))
  ;; which is equivalant to (s (c -pp1 rest))
  ;; which is created with compress-s-c
  ;; if the max/min val of (c -pp1 rest) is 0/-1,
  ;; then reducedp=1 and reduced=(-- (c -pp1 rest))
  ;; but it is decompressed so reduced=(sum pp1 (-- (c rest)))
  ;; reduced will be the value returned from create-s-instance right away.

  :returns (mv (reduced-pp-lst rp-term-listp
                               :hyp (and (rp-termp pp)
                                         (rp-termp c)))
               (reduced-c-lst rp-term-listp
                              :hyp (and (rp-termp pp)
                                        (rp-termp c)))
               (reducedp booleanp))
  (b* (((unless (s-pattern1-reduce-enabled))
        (mv nil nil nil)))
    (case-match c
      (('list ('c & ''nil c-pp &))
       (b* (((unless (pp-subsetp pp c-pp))
             (mv nil nil nil))
            (compressed (light-compress-s-c `(s '0 ,pp ,c))))
         (case-match compressed
           (('s & ''nil ('list single-c))
            (b* (((mv max min valid) (get-max-min-val single-c)))
              (cond  ((and valid
                           (= max 0)
                           (= min -1))
                      (b* (((mv res coughed-s coughed-pp) (decompress-s-c single-c))
                           ((unless (equal coughed-s ''nil))
                            (mv nil nil nil))
                           (coughed-pp (negate-list-instance coughed-pp)))
                        (mv (list-to-lst coughed-pp)
                            (list `(-- ,res))
                            t)))
                     #|((and valid
                     (= max 1)
                     (= min 0))
                     (b* (((mv res coughed-s coughed-pp) (decompress-s-c single-c))
                     ((unless (equal coughed-s ''nil))
                     (mv nil nil nil)))
                     (mv (list-to-lst coughed-pp)
                     (list res)
                     t)))||#
                     (t (mv nil nil nil)))))
           (& (mv nil nil nil)))))
      (& (mv nil nil nil)))))

;; (compress-s-c '(s '0 (list c b a) (list (c '0 'nil (list d c a) 'nil))))
;; (decompress-s-c '(S '0 (LIST B) (LIST (C '0 'NIL (LIST D (-- C) (-- A)) 'NIL))))

(define s-pattern2-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (mv (reduced-pp-lst rp-term-listp
                               :hyp (and (rp-termp pp)
                                         (rp-termp c)))
               (reducedp booleanp))
  (b* (((unless (and (equal c ''nil)
                     (pattern2-reduce-enabled)
                     (not (has-unflatenned-pp (list-to-lst pp)))))
        (mv nil nil))

       ;;(aggressive (pattern2-aggressive-reduce-enabled))
       )
    (case-match pp
      (('list ''1 pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 pp3))
            ((Unless success)
             (mv nil nil)))
         (mv (pp-sum-merge-aux (list ''1) (negate-lst new-pp-lst)) t)))
      (('list pp1 pp2 pp3)
       (b* (((unless (or
                      (equal pp1 ''1)
                      (and (and-subsetp pp2 pp1)
                           (and-subsetp pp3 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 pp3))
            ((Unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ;;(mv `(rp 'bitp (sum-list ,(create-list-instance new-pp-lst))) t)
      (('list pp1 pp2)
       (b* (((unless (or (equal pp1 ''1)
                         (and (and-subsetp pp2 pp1))))
             (mv nil nil))
            ((mv new-pp-lst success)
             (single-s-to-pp-lst pp1 pp2 ''0))
            ((Unless success)
             (mv nil nil)))
         (mv new-pp-lst t)))
      ;;(mv `(rp 'bitp (sum-list ,(create-list-instance new-pp-lst))) t)))
      (& (mv nil nil)))))

(progn
  (encapsulate
    (((pattern3-reduce-enabled) => *))
    (local
     (defun pattern3-reduce-enabled ()
       nil)))

  (defmacro enable-pattern3-reduce (enable)
    (if enable
        `(defattach  pattern3-reduce-enabled return-t)
      `(defattach  pattern3-reduce-enabled return-nil)))

  (enable-pattern3-reduce nil))

(define odd-many-ones (pp-lst)
  (cond ((atom pp-lst)
         nil)
        ((equal (car pp-lst) ''1)
         (not (odd-many-ones (cdr pp-lst))))
        (t nil))
  ///
  (defthm odd-many-ones-implies-consp
    (implies (odd-many-ones pp-lst)
             (and (consp pp-lst)
                  (equal (car pp-lst) ''1)))
    :rule-classes :forward-chaining))

(define s-pattern3-reduce ((pp rp-termp)
                           (c rp-termp))
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-termp pp)
                                     (rp-termp c)))
               (reducedp booleanp))
  :prepwork
  ((local
    (defthm lemma1
      (implies (rp-term-listp lst)
               (rp-term-listp (cdr lst))))))

  (b* (((unless (and
                 (pattern3-reduce-enabled)
                 (odd-many-ones (list-to-lst pp))))
        (mv nil nil nil))
       (pp-lst (list-to-lst pp))
       ((unless (odd-many-ones pp-lst))
        (mv nil nil nil))
       (rest-pp-lst (cdr pp-lst))
       (new-pp (create-list-instance rest-pp-lst))
       (single-s `(rp 'bitp (s ',(calculate-s-hash new-pp c)
                               ,new-pp
                               ,c))))
    (mv (list `(-- ,single-s))
        (list ''1)
        t)))

(progn
  (define single-c-mergeable ((single-c1 rp-termp)
                              (single-c2 rp-termp))
    (b* (((when (or (negated-termp single-c1)
                    (negated-termp single-c2)))
          nil)
         ((mv c1-hash-code ?s-arg1 ?pp-arg1 ?c-arg1-lst type1) (get-c-args single-c1))
         ((mv &            ?s-arg2 ?pp-arg2 ?c-arg2-lst type2) (get-c-args single-c2))
         ((when (or (not type1) (not type2)))
          (progn$ (hard-error
                   'single-c-mergeable
                   "Unexpected single-c instances.~%single-c1:~p0~%single-c2:~p1~%"
                   (list (cons #\0 (list type1 single-c1))
                         (cons #\1 (list type2 single-c2))))
                  nil))
         ((unless (case-match s-arg2 (('list . &) t)))
          nil)
         ;; search for a merge potential by going through s-lst of the single-c2
         ;; when a match is found, that s will be removed from the list.
         ((mv & success)
          (single-c-try-merge-params (cdr s-arg2)
                                     c1-hash-code
                                     s-arg1
                                     pp-arg1
                                     c-arg1-lst)))
      success))
  (DEFBADGE RP-EQUAL-CNT)
  (defwarrant EX-FROM-RP$$INLINE)
  (defwarrant EX-FROM-RP)
  (DEFBADGE EX-FROM-RP/--)
  (defwarrant LOGAPP)
  (DEFBADGE ACL2::EXPLODE$INLINE)
  (DEFBADGE PP-LIST-ORDER-AUX)
  (DEFBADGE GET-SYMBOL-HASH)
  (defwarrant AND-LIST-HASH-aux)
  (defwarrant AND-LIST-HASH)
  (defwarrant PP-LIST-ORDER)
  (defwarrant PP-ORDER)
  (defwarrant PP-ORDER-AND-NEGATED-TERMSP)
  (defwarrant PP-SUM-MERGE-AUX)
  (defwarrant CREATE-LIST-INSTANCE)
  (defwarrant LIST-TO-LST)
  (DEFBADGE S-SUM-MERGE-AUX)
  (DEFBADGE LIGHT-S-OF-S-FIX-LST)
  (defwarrant LIGHT-S-OF-S-FIX)
  (defwarrant RP-EQUAL-CNT-SUBTERMS)

  (defwarrant SINGLE-C-TRY-MERGE-PARAMS-AUX$INLINE)
  (defwarrant SINGLE-C-TRY-MERGE-PARAMS)
  (defwarrant GET-C-ARGS$INLINE)
  (defwarrant negated-termp$inline)
  (defwarrant single-c-mergeable)

  (define not-well-merged-c-lst ((c-lst rp-term-listp))
    :prepwork
    ((local
      (in-theory (e/d ( (:definition acl2::apply$-badgep)
                        (:linear acl2::apply$-badgep-properties . 1)
                        (:definition subsetp-equal)
                        (:definition member-equal)
                        (:rewrite
                         acl2::member-equal-newvar-components-1))
                      ()))))
    (loop$ for x in c-lst when :guard (and (rp-term-listp c-lst)
                                           (rp-termp x))
           (loop$ for y in c-lst
                  when :guard (and (rp-term-listp c-lst)
                                   (rp-termp y)
                                   (rp-termp x))
                  (and
                   (not (equal x y))
                   (single-c-mergeable x y))
                  collect t)
           collect t)))

(define create-c-instance ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp)
                           ;;(s-coughed-lst rp-term-listp)
                           ;;(pp-coughed-lst rp-term-listp)
                           )
;:inline t
  :returns (mv (res-s-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    ;;(rp-term-listp s-coughed-lst)
                                    ;;(rp-term-listp pp-coughed-lst)
                                    ))
               (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)
                                     ;;(rp-term-listp s-coughed-lst)
                                     ;;(rp-term-listp pp-coughed-lst)
                                     ))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    ;;(rp-term-listp s-coughed-lst)
                                    ;;(rp-term-listp pp-coughed-lst)
                                    )))
  (b* (#|(- (and (not-well-merged-c-lst c-lst)
       (hard-error 'create-c-instance
       "Mergable c-lst ~p0 ~%"
       (list (cons #\0 c-lst)))))||#

       (reducedp (c-pattern0-reduce s-lst pp-lst c-lst))
       ((when reducedp)
        (mv nil nil nil))

       ((mv s-lst pp-lst c-lst)
        (c-pattern1-reduce s-lst pp-lst c-lst))
       ((mv reduced-pp-lst reducedp)
        (c-pattern2-reduce s-lst pp-lst c-lst))
       ((when reducedp)
        (mv nil reduced-pp-lst nil))
       #|((mv reduced-s-lst reduced-pp-lst reduced-c-lst reducedp)
       (c-pattern3-reduce s-lst pp-lst c-lst))||#
       #|((when reducedp)
       (mv reduced-s-lst reduced-pp-lst reduced-c-lst))||#)
    (cond ((or (and (equal c-lst nil)
                    (equal s-lst nil)
                    (case-match pp-lst
                      ((('and-list & &)) t)))
               (and (equal c-lst nil)
                    (equal pp-lst nil)
                    (case-match s-lst
                      ((('s & & &)) t)
                      ((('rp ''bitp &)) t)))
               (and (equal s-lst nil)
                    (equal pp-lst nil)
                    (case-match c-lst
                      ((single-c)
                       (or (has-bitp-rp single-c)
                           (is-c-bitp-traverse single-c))))))
           (mv nil nil nil))
          ((and (quoted-listp s-lst)
                (quoted-listp pp-lst)
                (quoted-listp c-lst))
           (b* ((res
                 `',(c 0
                       (unquote-all s-lst)
                       (unquote-all pp-lst)
                       (unquote-all c-lst))))
             (if (equal res ''0)
                 (mv nil nil nil)
               (mv nil (list res) nil))))
          (t
           (b* ((s (create-list-instance s-lst))
                (pp (create-list-instance pp-lst))
                (c (create-list-instance c-lst))
                (hash-code (calculate-c-hash s pp c))

                (res `(c ',hash-code ,s ,pp ,c))
                ((mv max-val min-val valid)
                 (if (natp (maybe-bitp-precheck res)) ;; minimize the calls made to get-max-min-val
                     (get-max-min-val res)
                   #|(progn$ ;;(cw " " (maybe-bitp-precheck res))
                   (b* (((mv mx mn valid) (get-max-min-val res)))
                   (progn$
                   (and (or (not valid)
                   (not (equal mx 1))
                   (not (equal mn 0)))
                   (cw "max:~p0 min:~p1 valid:~p2 maybe:~p3~%" mx mn
                   valid (maybe-bitp-precheck res)))
                   (mv mx mn valid))))|#
                   (mv 0 0 nil)))
                ((when (and valid
                            (equal max-val 1)
                            (equal min-val 0)))
                 (mv nil nil (list `(rp 'bitp ,res))))

                ((when (and valid
                            (equal max-val 0)
                            (equal min-val 0)))
                 (mv nil nil nil))

                )
             (mv nil nil (list res)))))))

;;(memoize 'get-max-min-val :condition '(single-c-p (ex-from-rp-loose term)))
(profile 'get-max-min-val)

(define create-s-instance ((pp rp-termp)
                           (c rp-termp))
  ;;:inline t
  :returns (mv (s-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c)))
               (pp-res-lst rp-term-listp
                           :hyp (and (rp-termp pp)
                                     (rp-termp c)))
               (c-res-lst rp-term-listp
                          :hyp (and (rp-termp pp)
                                    (rp-termp c))))
  (b* ((reducedp (s-pattern0-reduce pp c))
       ((when reducedp)
        (mv nil nil nil))
       ((mv reduced-pp-lst reduced-c-lst reducedp)
        (s-pattern1-reduce pp c))
       ((when reducedp)
        (mv nil reduced-pp-lst reduced-c-lst))
       ((mv reduced-pp-lst reducedp)
        (s-pattern2-reduce pp c))
       ((when reducedp)
        (mv nil reduced-pp-lst nil))
       ((mv reduced-s-lst reduced-pp-lst reducedp)
        (s-pattern3-reduce pp c))
       ((when reducedp)
        (mv reduced-s-lst reduced-pp-lst nil))
       )
    (cond ((and (quotep pp)
                (quotep c)
                (consp (cdr pp))
                (consp (cdr c)))
           (b* ((res `',(s 0 (unquote pp) (unquote c))))
             (if (equal res ''0)
                 (mv nil nil nil)
               (mv nil (list res) nil))))
          ((and (all-quoted-list pp)
                (all-quoted-list c))
           (mv nil
               (list `',(s 0
                           (unquote-all (list-to-lst pp))
                           (unquote-all (list-to-lst c))))
               nil))
          ((and (equal c ''nil)
                (case-match pp (('list e)
                                (b* ((e-ex (ex-from-rp$ e)))
                                  (or* (and-list-p e-ex)
                                       (logbit-p e-ex)
                                       (binary-fnc-p e-ex)
                                       (has-bitp-rp e))))))
           (mv nil (list (cadr pp)) nil))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (or (has-bitp-rp single-c)))))
           (mv nil nil (list (cadr c))))
          ((and (equal pp ''nil)
                (case-match c
                  (('list single-c)
                   (is-c-bitp-traverse single-c))))
           (mv nil nil (list `(rp 'bitp ,(cadr c)))))
          (t
           (mv (list `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c)))
               nil
               nil)))))

;;:i-am-here

(define swap-c-lsts (c1-lst c2-lst enabled)
  :inline t
  :returns (mv (res1 rp-term-listp
                     :hyp (and (rp-term-listp c1-lst)
                               (rp-term-listp c2-lst)))
               (res2 rp-term-listp
                     :hyp (and (rp-term-listp c1-lst)
                               (rp-term-listp c2-lst))))
  (b* (((unless enabled)
        (mv c1-lst c2-lst))
       (first-id  (case-match c1-lst
                    ((('c ('quote hash) . &) . &) hash)
                    (& 0)))
       (second-id (case-match c2-lst
                    ((('c ('quote hash) . &) . &) hash)
                    (& 0)))
       (len2 (len c2-lst))
       (len1 (len c1-lst))
       (swap (if (= len1 len2)
                 (> (nfix first-id)
                    (nfix second-id))
               (> len1 len2))))
    (if swap
        (mv c2-lst c1-lst)
      (mv c1-lst c2-lst))))

;; (acl2::defines
;;  count-c
;;  :flag-defthm-macro defthm-count-c
;;  :flag-local nil
;;  :hints (("Goal"
;;           :in-theory (e/d (measure-lemmas
;;                            single-c-p
;;                            single-s-p)
;;                           ())))
;;  (define count-c (term)
;;    :measure (cons-count term)

;;    (b* ((term (ex-from-rp term)))
;;      (cond
;;       ((single-c-p term)
;;        (let ((arg-c (car (cddddr term))))
;;          (case-match arg-c
;;            (('list . c-lst) (1+ (count-c-lst c-lst)))
;;            (& 1))))
;;       ((single-s-p term)
;;        (let ((arg-c (car (cdddr term))))
;;          (case-match arg-c
;;            (('list . c-lst) (count-c-lst c-lst))
;;            (& 0))))
;;       ((or (atom term) (quotep term)) 0)
;;       (t (count-c-lst (cdr term))))))
;;  (define count-c-lst (lst)
;;    :measure (cons-count lst)
;;    (if (atom lst)
;;        0
;;      (+ (count-c-lst (cdr lst))
;;         (count-c (car lst))))))

;; (local
;;  (encapsulate
;;    nil
;;    (defthm c-sum-merge-m-lemma1
;;      (EQUAL (+ (COUNT-C-LST (MV-NTH 0 (swap-c-lsts C1-LST C2-LST cond)))
;;                (COUNT-C-LST (MV-NTH 1 (swap-c-lsts C1-LST C2-LST cond))))
;;             (+ (COUNT-C-LST C1-LST)
;;                (COUNT-C-LST C2-LST)))
;;      :hints (("Goal"
;;               :in-theory (e/d (swap-c-lsts) ()))))

;;    (defthm c-sum-merge-m-lemma2
;;      (implies (and (MV-NTH 4 (GET-C-ARGS SINGLE-C1))
;;                    (MV-NTH 4 (GET-C-ARGS SINGLE-C2))
;;                    (EQUAL (CAR (MV-NTH 1 (GET-C-ARGS SINGLE-C2)))
;;                           'LIST))
;;               (< (+ (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C1)))
;;                     (COUNT-C-LST (MV-NTH 3 (GET-C-ARGS SINGLE-C2))))
;;                  (+ (COUNT-C SINGLE-C1)
;;                     (COUNT-C SINGLE-C2))))
;;      :hints (("Goal"
;;               :do-not-induct t
;;               :expand ((COUNT-C SINGLE-C1)
;;                        (COUNT-C SINGLE-C2))
;;               :in-theory (e/d (GET-C-ARGS
;;                                SINGLE-C-P
;;                                SINGLE-s-P)
;;                               ()))))

;;    (defthm c-sum-merge-m-lemma3
;;      (IMPLIES (AND (CONSP C2-LST))
;;               (and (<= (COUNT-C-LST (CDR C2-LST))
;;                        (COUNT-C-LST C2-LST))
;;                    (>= (COUNT-C-LST C2-LST)
;;                        (COUNT-C-LST (CDR C2-LST)))))
;;      :hints (("Goal"
;;               :expand (COUNT-C-LST C2-LST)
;;               :in-theory (e/d () ()))))

;;    (defthm c-sum-merge-m-lemma4
;;      (IMPLIES (AND (CONSP C1-LST))
;;               (<= (+ a (COUNT-C (CAR C1-LST)))
;;                   (+ (COUNT-C-LST C1-LST) a)))
;;      :hints (("Goal"
;;               :expand (COUNT-C-LST C1-LST)
;;               :in-theory (e/d () ()))))

;;    (defthm c-sum-merge-m-lemma5
;;      (IMPLIES (AND (CONSP C1-LST)
;;                    (<= (+ (COUNT-C-LST C1-LST)
;;                           (COUNT-C-LST C2-LST))
;;                        (+ (COUNT-C-LST C2-LST)
;;                           (COUNT-C (CAR C1-LST)))))
;;               (EQUAL (+ (COUNT-C-LST C2-LST)
;;                         (COUNT-C (CAR C1-LST)))
;;                      (+ (COUNT-C-LST C1-LST)
;;                         (COUNT-C-LST C2-LST))))
;;      :hints (("Goal"
;;               :use ((:instance c-sum-merge-m-lemma4
;;                                (a (COUNT-C-LST C2-LST))))
;;               :in-theory (e/d () (c-sum-merge-m-lemma4)))))

;;    (defthm c-sum-merge-m-lemma6
;;      (implies (consp c2-lst)
;;               (>= (COUNT-C-LST C2-LST)
;;                   (COUNT-C (CAR C2-LST))))
;;      :hints (("Goal"
;;               :expand (COUNT-C-LST C2-LST)
;;               :in-theory (e/d () ()))))

;;    (defthm c-sum-merge-m-lemma7
;;      (implies (and (consp c2-lst)
;;                    (<= (count-c-lst c2-lst)
;;                        (count-c (car c2-lst))))
;;               (equal (+ (count-c single-c1)
;;                         (count-c (car c2-lst)))
;;                      (+ (count-c single-c1)
;;                         (count-c-lst c2-lst))))
;;      :hints (("Goal"
;;               :use ((:instance c-sum-merge-m-lemma6))
;;               :in-theory (e/d () (c-sum-merge-m-lemma6)))))

;;    (defthm c-sum-merge-m-lemma8
;;      (IMPLIES (AND (CONSP C2-LST)
;;                    (<= (COUNT-C-LST C2-LST)
;;                        (COUNT-C-LST (CDR C2-LST))))
;;               (equal (COUNT-C-LST C2-LST)
;;                      (COUNT-C-LST (CDR C2-LST))))
;;      :hints (("Goal"
;;               :expand (COUNT-C-LST C2-LST)
;;               :in-theory (e/d () ()))))

;;    ))

(define c-of-1-merge ((single-c1 rp-termp)
                      (single-c2 rp-termp))
  :returns (mv (res-s-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                  (rp-termp single-c2)))
               (res-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                   (rp-termp single-c2)) )
               (res-c-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                  (rp-termp single-c2)))
               (merge-success booleanp))
  :verify-guards nil
  (b* (((mv single-c1 negated-c1)
        (if (negated-termp single-c1) (mv (cadr single-c1) t) (mv single-c1 nil)))
       ((mv single-c2 negated-c2)
        (if (negated-termp single-c2) (mv (cadr single-c2) t) (mv single-c2 nil)))
       ((mv c1-hash-code s-arg1 pp-arg1 c-arg1-lst type1)
        (get-c-args single-c1))
       ((mv c2-hash-code s-arg2 pp-arg2 c-arg2-lst type2)
        (get-c-args single-c2))
       ((when (or (not type1) (not type2)))
        (progn$ (hard-error
                 'c-of-1-merge
                 "Unexpected single-c instances.~%single-c1:~p0~%single-c2:~p1~%"
                 (list (cons #\0 (list type1 single-c1))
                       (cons #\1 (list type2 single-c2))))
                (mv nil nil nil nil))))
    (cond ((and (or (= (hash-coef) 0) (= c1-hash-code (+ 5 c2-hash-code)))
                (consp (list-to-lst pp-arg1))
                (equal (car (list-to-lst pp-arg1)) ''1)
                (equal s-arg1 s-arg2)
                (equal (cdr (list-to-lst pp-arg1))
                       (list-to-lst pp-arg2))
                (equal c-arg1-lst c-arg2-lst))
           (cond ((and negated-c1
                       negated-c2)
                  (mv (negate-lst (list-to-lst s-arg1))
                      (negate-lst (list-to-lst pp-arg2))
                      (negate-lst c-arg1-lst)
                      t))
                 ((and (not negated-c1)
                       negated-c2)
                  (b* (((unless (equal s-arg2 ''nil))
                        (mv nil nil nil nil))
                       ((mv new-s-lst new-pp-lst new-c-lst)
                        (create-s-instance pp-arg2
                                           (create-list-instance c-arg2-lst))))
                    (mv new-s-lst
                        new-pp-lst new-c-lst
                        t)))
                 ((and (not negated-c2)
                       negated-c1)
                  (b* (((unless (equal s-arg2 ''nil))
                        (mv nil nil nil nil))
                       ((mv new-s-lst new-pp-lst new-c-lst)
                        (create-s-instance pp-arg2
                                           (create-list-instance c-arg2-lst))))
                    (mv (negate-lst new-s-lst)
                        (negate-lst new-pp-lst)
                        (negate-lst new-c-lst)
                        t)))
                 (t
                  (mv (list-to-lst s-arg1) (list-to-lst pp-arg2) c-arg1-lst
                      t))))
          ((and (or (= (hash-coef) 0) (= c2-hash-code (+ 5 c1-hash-code)))
                (consp (list-to-lst pp-arg2))
                (equal (car (list-to-lst pp-arg2)) ''1)
                (equal s-arg1 s-arg2)
                (equal (cdr (list-to-lst pp-arg2))
                       (list-to-lst pp-arg1))
                (equal c-arg1-lst c-arg2-lst))
           (cond ((and negated-c1 negated-c2)
                  (mv (negate-lst (list-to-lst s-arg2))
                      (negate-lst (list-to-lst pp-arg1))
                      (negate-lst c-arg1-lst)
                      t))
                 ((and (not negated-c2) negated-c1)
                  (b* (((unless (equal s-arg1 ''nil))
                        (mv nil nil nil nil))
                       ((mv new-s-lst new-pp-lst new-c-lst)
                        (create-s-instance pp-arg1
                                           (create-list-instance c-arg2-lst))))
                    (mv new-s-lst
                        new-pp-lst new-c-lst
                        t)))
                 ((and (not negated-c1) negated-c2)
                  (b* (((unless (equal s-arg2 ''nil))
                        (mv nil nil nil nil))
                       ((mv new-s-lst new-pp-lst new-c-lst)
                        (create-s-instance pp-arg1
                                           (create-list-instance c-arg2-lst))))
                    (mv (negate-lst new-s-lst)
                        (negate-lst new-pp-lst)
                        (negate-lst new-c-lst)
                        t)))
                 (t
                  (mv (list-to-lst s-arg1) (list-to-lst pp-arg1) c-arg1-lst
                      t))))
          (t
           (mv nil nil nil nil))))
  ///
  (verify-guards c-of-1-merge
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ())))))

(acl2::defines
  c-sum-merge
  :flag-defthm-macro defthm-c-sum-merge
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))

  (define single-c-try-merge  ((single-c1 rp-termp)
                               (single-c2 rp-termp)
                               &key (limit 'limit))
    ;; returns (mv coughed-s coughed-pp-lst produced-c-lst merge-success)
    ;; if merge-success is t
    ;; otherwise (mv nil nil 0 merge-success)
    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c single-c1) (count-c single-c2))
    ;;            0 0))
    ;;:inline t
    :guard (natp limit)
    :measure (nfix limit)
    :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                               (rp-termp single-c2)))
                 (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-termp single-c2)) )
                 (produced-c-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-termp single-c2)))
                 (merge-success booleanp))
    :no-function t
    (if (zp limit)
        (mv ''nil nil nil nil)
      (let ((limit (1- limit)))
        (b* (;; don't try to merge negated elements. They will be coughed off and
             ;; will be tried later.

             ((mv s-lst pp-lst c-lst merge-success)
              (c-of-1-merge single-c1 single-c2))
             ((when merge-success)
              (mv (create-list-instance s-lst) pp-lst c-lst t))

             ((when (or (negated-termp single-c1)
                        (negated-termp single-c2)))
              (mv ''nil nil nil nil ))
             ((mv c1-hash-code s-arg1 pp-arg1 c-arg1-lst type1) (get-c-args single-c1))
             ((mv &            s-arg2 pp-arg2 c-arg2-lst type2) (get-c-args single-c2))
             ((when (or (not type1) (not type2)))
              (progn$ (hard-error
                       'single-c-try-merge
                       "Unexpected single-c instances.~%single-c1:~p0~%single-c2:~p1~%"
                       (list (cons #\0 (list type1 single-c1))
                             (cons #\1 (list type2 single-c2))))
                      (mv ''nil nil nil nil )))
             ((unless (case-match s-arg2 (('list . &) t)))
              (mv ''nil nil nil nil ))
             ;; search for a merge potential by going through s-lst of the single-c2
             ;; when a match is found, that s will be removed from the list.
             ((mv updated-s-arg2-lst success)
              (single-c-try-merge-params (cdr s-arg2)
                                         c1-hash-code
                                         s-arg1
                                         pp-arg1
                                         c-arg1-lst))
             ;; no match? move on..
             ((unless success)
              (mv ''nil nil nil nil ))
             ;; if it reached here, then it  means it can merge. Eviscerate single-c1
             ;; and merge its arguments:
             ;; first merge c-arguments. It might cough out s and pp lists, and a
             ;; c-lst to be coughed
             ((mv arg-coughed-s arg-coughed-pp-lst arg-merged-c-lst
                  arg-to-be-coughed-c-lst)
              (c-sum-merge c-arg1-lst c-arg2-lst))

             ;; create the new pp arg by merging the coughed-pp from c-merger, and
             ;; pp-args from the original single-c1 and single-c2
             (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg1) (list-to-lst pp-arg2)))
             (pp-lst (pp-sum-merge-aux arg-coughed-pp-lst pp-lst))

             ;; also merge the updated s-lst of single-c2 and coughed s-lst.
             ;; and s-arg1 if any (it will be ''nil most of the time)
             ;; before creating the c instance, try coughing out with the new s argument
             (new-s-arg-lst (s-sum-merge-aux (list-to-lst s-arg1)
                                             (s-sum-merge-aux (list-to-lst arg-coughed-s)
                                                              updated-s-arg2-lst)))

             ((mv coughed-s-lst new-s-arg-lst)
              (c-fix-arg-aux new-s-arg-lst t))

             ((mv coughed-pp-lst new-pp-lst)
              (c-fix-arg-aux-with-cond pp-lst t (clean-pp-args-cond new-s-arg-lst arg-merged-c-lst)))

             ;; To-be-coughed c-lst from the args is the coughed-c-lst of the
             ;; new c instance.
             ((mv merged-s-lst merged-pp-lst merged-c-lst)
              (create-c-instance new-s-arg-lst new-pp-lst arg-merged-c-lst))

             (coughed-s-lst (s-sum-merge-aux coughed-s-lst merged-s-lst))
             (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst merged-pp-lst))
             (produced-c-lst (append arg-to-be-coughed-c-lst merged-c-lst)))
          (mv (create-list-instance coughed-s-lst)
              coughed-pp-lst
              produced-c-lst
              t)))))

  (define c-sum-merge-lst-aux ((single-c1 rp-termp)
                               (c2-lst rp-term-listp)
                               &key (limit 'limit))
    ;;:returns (mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst merge-success)

    ;; try and merge single-c1 with something in c2-lst
    ;; after the merge, coughed-s and coughed-pp-lst might have results from the
    ;; new c.
    ;; the result "produced-c-lst" may be mergable with something(s) in
    ;; rest-c2-lst
    ;; when merge is succesful c2-lst will have one less element.
    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c single-c1) (count-c-lst c2-lst))
    ;;            1
    ;;            (acl2-count c2-lst)))
    :guard (natp limit)
    :measure (nfix limit)
    :no-function t
    :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                               (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-term-listp c2-lst)))
                 (produced-c-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-term-listp c2-lst)))
                 (updated-c2-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-term-listp c2-lst)))
                 (merge-success booleanp)
                 )
    (if (zp limit)
        (mv ''nil nil nil (cons single-c1 c2-lst) nil)
      (let ((limit (1- limit)))
        (b* (((when (atom c2-lst))
              (mv ''nil nil nil c2-lst nil ))
             ((mv coughed-s coughed-pp-lst  produced-c-lst merge-success)
              (single-c-try-merge single-c1 (car c2-lst)))
             ((when merge-success)
              (mv coughed-s coughed-pp-lst produced-c-lst (cdr c2-lst)
                  merge-success ))

             ((mv coughed-s coughed-pp-lst produced-c-lst merge-success)
              (single-c-try-merge (car c2-lst) single-c1))

             ((when merge-success)
              (mv coughed-s coughed-pp-lst  produced-c-lst (cdr c2-lst)
                  merge-success ))

             ((mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst
                  merge-success)
              (c-sum-merge-lst-aux single-c1 (cdr c2-lst))))
          (if merge-success
              (mv coughed-s coughed-pp-lst produced-c-lst (cons (car c2-lst) rest-c2-lst)
                  merge-success )
            (mv ''nil nil nil c2-lst nil ))))))

  (define c-sum-merge-lst ((single-c1 rp-termp)
                           (c2-lst rp-term-listp)
                           &key (limit 'limit))
    ;;:inline t
    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c single-c1) (count-c-lst c2-lst))
    ;;            2 0))
    :guard (natp limit)
    :measure (nfix limit)
    :returns (mv (coughed-s rp-termp :hyp (and (rp-termp single-c1)
                                               (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                         (rp-term-listp c2-lst)))
                 (new-c2-lst rp-term-listp :hyp (and (rp-termp single-c1)
                                                     (rp-term-listp c2-lst)))
                 )
    :no-function t
    ;; Same as c-sum-merge-lst-aux but produced-c-lst is not mergable with anything
    ;; in rest-c2-lst because it was tried to be merged as long as it goes.
    (if (zp limit)
        (mv ''nil nil (cons single-c1 c2-lst) )
      (let ((limit (1- limit)))
        (b* (((when (equal single-c1 ''0)) ;; if it is 0 then convert it to a pp
              (mv ''nil nil c2-lst ))
             ((when (quotep single-c1)) ;; if it is quoted then convert it to a pp
              (mv ''nil (list single-c1) c2-lst ))

             ((mv coughed-s coughed-pp-lst produced-c-lst rest-c2-lst
                  merge-success)
              (c-sum-merge-lst-aux single-c1 c2-lst)))
          (if merge-success
              (b* ( #|((unless (mbt (< (+ (count-c-lst produced-c-lst) (count-c-lst rest-c2-lst))
                   (+ (count-c single-c1) (count-c-lst c2-lst))))) ; ;
                   (mv coughed-s coughed-pp-lst  (s-sum-merge-aux produced-c-lst rest-c2-lst)))||#
                   ((mv coughed-s2 coughed-pp-lst2 new-c2-lst)
                    (c-sum-merge-lst-lst produced-c-lst rest-c2-lst))
                   (coughed-s (s-sum-merge coughed-s coughed-s2))
                   (coughed-pp-lst (pp-sum-merge-aux  coughed-pp-lst coughed-pp-lst2)))
                (mv coughed-s coughed-pp-lst  new-c2-lst))
            (mv ''nil nil (s-sum-merge-aux (list single-c1) c2-lst)))))))

  (define c-sum-merge-lst-lst ((c1-lst rp-term-listp)
                               (c2-lst rp-term-listp)
                               &key (limit 'limit))
    ;;:returns (mv coughed-s coughed-pp-lst-lst c2-lst)

    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
    ;;            3
    ;;            (acl2-count c1-lst)))
    :guard (natp limit)
    :measure (nfix limit)
    :returns (mv (coughed-s rp-termp :hyp (and (rp-term-listp c1-lst)
                                               (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp :hyp (and (rp-term-listp c1-lst)
                                                         (rp-term-listp
                                                          c2-lst)))
                 (updated-c2-lst rp-term-listp :hyp (and (rp-term-listp c1-lst)
                                                         (rp-term-listp
                                                          c2-lst)))
                 )
    :no-function t
    (if (zp limit)
        (mv ''nil nil (acl2::append-without-guard c1-lst c2-lst))
      (let ((limit (1- limit)))
        (b* (((when (atom c1-lst))
              (mv ''nil nil c2-lst ))

             ((mv coughed-s coughed-pp-lst1 updated-c2-lst)
              (c-sum-merge-lst (car c1-lst) c2-lst))

             #|((unless (mbt (<= (+ (count-c-lst (cdr c1-lst)) (count-c-lst updated-c2-lst))
             (+ (count-c-lst c1-lst) (count-c-lst c2-lst))))) ;
             (mv coughed-s coughed-pp-lst1 (s-sum-merge-aux (cdr c1-lst) updated-c2-lst)))||#

             ((mv coughed-s2 coughed-pp-lst2  updated2-c2-lst)
              (c-sum-merge-lst-lst (cdr c1-lst) updated-c2-lst))

             (coughed-s-merged (s-sum-merge coughed-s coughed-s2))
             (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst1
                                               coughed-pp-lst2)))
          (mv coughed-s-merged
              coughed-pp-lst
              updated2-c2-lst
              )))))

  (define c-sum-merge ((c1-lst rp-term-listp)
                       (c2-lst rp-term-listp)
                       &key
                       (auto-swap 't)
                       (clean-c1-lst 'nil)
                       (cough-c-lst 't)
                       (limit 'limit))
    ;;:inline t
    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-term-listp c1-lst)
                                      (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp
                                 :hyp (and (rp-term-listp c1-lst)
                                           (rp-term-listp c2-lst)))
                 (c-merged-lst rp-term-listp
                               :hyp (and (rp-term-listp c1-lst)
                                         (rp-term-listp c2-lst)))
                 (to-be-coughed-c-lst rp-term-listp
                                      :hyp (and (rp-term-listp c1-lst)
                                                (rp-term-listp c2-lst)))
                 )
    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
    ;;            5 0))
    :guard (natp limit)
    :measure (nfix limit)
    :no-function t
    (if (zp limit)
        (mv ''nil nil (acl2::append-without-guard c1-lst c2-lst) nil)
      (let ((limit (1- limit)))
        (b* (((mv c1-lst c2-lst)
              (swap-c-lsts c1-lst c2-lst auto-swap)))
          (c-sum-merge-aux c1-lst c2-lst
                           :clean-c1-lst clean-c1-lst
                           :cough-c-lst cough-c-lst
                           )))))

  (define c-sum-merge-aux ((c1-lst rp-term-listp)
                           (c2-lst rp-term-listp)
                           &key
                           (clean-c1-lst 'nil)
                           (cough-c-lst 't)
                           (limit 'limit))
    ;; returns (mv coughed-s coughed-pp-lst res-c)
    ;; :measure (acl2::nat-list-measure
    ;;           (list
    ;;            (+ (count-c-lst c1-lst) (count-c-lst c2-lst))
    ;;            4 0))
    :guard (natp limit)
    :measure (nfix limit)
    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-term-listp c1-lst)
                                      (rp-term-listp c2-lst)))
                 (coughed-pp-lst rp-term-listp
                                 :hyp (and (rp-term-listp c1-lst)
                                           (rp-term-listp c2-lst)))
                 (c-merged-lst rp-term-listp
                               :hyp (and (rp-term-listp c1-lst)
                                         (rp-term-listp c2-lst)))
                 (to-be-coughed-c-lst rp-term-listp
                                      :hyp (and (rp-term-listp c1-lst)
                                                (rp-term-listp c2-lst)))
                 )
    :no-function t
    (if (zp limit)
        (mv ''nil nil (acl2::append-without-guard c1-lst c2-lst) nil)
      (let ((limit (1- limit)))
        (cond ((equal c1-lst nil)
               (mv ''nil nil c2-lst nil ))
              ((and (equal c2-lst nil)
                    (not clean-c1-lst))
               (mv ''nil nil c1-lst nil ))
              (t (b* (((mv coughed-s coughed-pp-lst merged-c-lst)
                       (c-sum-merge-lst-lst c1-lst c2-lst))
                      ((mv to-be-coughed-c-lst merged-c-lst)
                       (if cough-c-lst
                           (cough-duplicates merged-c-lst)
                         (mv nil merged-c-lst))))
                   (mv coughed-s coughed-pp-lst merged-c-lst to-be-coughed-c-lst)))))))
  ///
  (verify-guards c-sum-merge-aux-fn))

;;;;;;;;;;

(acl2::memoize-partial
 ((single-c-try-merge* single-c-try-merge-fn)
  (c-sum-merge-lst-aux* c-sum-merge-lst-aux-fn)
  (c-sum-merge-lst* c-sum-merge-lst-fn)
  (c-sum-merge-lst-lst* c-sum-merge-lst-lst-fn)
  (c-sum-merge* c-sum-merge-fn)
  (c-sum-merge-aux* c-sum-merge-aux-fn
                    :condition t
                    :memo-table-init-size 1000000
                    :aokp t))
 :condition nil)

(progn
  (encapsulate
    (((c-of-s-fix-mode) => *))
    (local
     (defun c-of-s-fix-mode ()
       nil)))

  (defmacro enable-c-of-s-fix-mode (enabled)
    (if enabled
        `(progn
           (defattach  c-of-s-fix-mode return-t))
      `(progn
         (defattach  c-of-s-fix-mode return-nil))))

  (enable-c-of-s-fix-mode t))

;; :i-am-here

;; (define c-sum-merge-light ((c1-lst rp-term-listp)
;;                            (c2-lst rp-term-listp))

(define c-sum-merge-main ((c1-lst rp-term-listp)
                          (c2-lst rp-term-listp)
                          &key
                          (auto-swap 't)
                          (clean-c1-lst 'nil)
                          (cough-c-lst 't)
                          (clean-args-for-s 'nil))
  :returns (mv (coughed-s rp-termp
                          :hyp (and (rp-term-listp c1-lst)
                                    (rp-term-listp c2-lst)))
               (coughed-pp-lst rp-term-listp
                               :hyp (and (rp-term-listp c1-lst)
                                         (rp-term-listp c2-lst)))
               (c-merged-lst rp-term-listp
                             :hyp (and (rp-term-listp c1-lst)
                                       (rp-term-listp c2-lst)))
               (to-be-coughed-c-lst rp-term-listp
                                    :hyp (and (rp-term-listp c1-lst)
                                              (rp-term-listp c2-lst)))
               )
  (b* (((unless (c-of-s-fix-mode))
        (c-sum-merge* c1-lst c2-lst auto-swap clean-c1-lst cough-c-lst))
       (merged-c-lst (if clean-args-for-s
                         (sum-merge-lst-for-s c1-lst c2-lst)
                       (s-sum-merge-aux c1-lst c2-lst)))
       #|(- (or (s-sum-ordered-listp c1-lst)
       (hard-error 'c-sum-merge-main
       "c1-lst is not ordered. ~p0 ~%"
       (list (cons #\0 c1-lst)))))
       (- (or (s-sum-ordered-listp c2-lst)
       (hard-error 'c-sum-merge-main
       "c2-lst is not ordered. ~p0 ~%"
       (list (cons #\0 c2-lst)))))
       (- (or (s-sum-ordered-listp merged-c-lst)
       (hard-error 'c-sum-merge-main
       "merged-c-lst is not ordered. ~p0. c1-lst: ~p1
       c2-lst: ~p2 ~%"
       (list (cons #\0 merged-c-lst)
       (cons #\1 c1-lst)
       (cons #\2 c2-lst)))))||#)
    (mv ''nil nil merged-c-lst nil)))

(define add-c-rp-bitp ((lst rp-term-listp))
  :returns (res rp-term-listp :hyp (rp-term-listp lst))
  (if (atom lst)
      nil
    (cons-with-hint (if (and (is-rp (car lst))
                             (equal (cadr (car lst)) ''bitp))
                        (car lst)
                      (if (and (consp (car lst))
                               (equal (car lst) '--))
                          (car lst)
                        (progn$ (cw "adding a bitp tp byproduct c ~p0 ~%" (car lst))
                                (hard-error 'add-c-rp-bitp "" nil)
                                `(rp 'bitp ,(car lst)))))
                    (add-c-rp-bitp (cdr lst))
                    lst)))

(define c-of-s-fix-lst ((arg-s-lst rp-term-listp)
                        (arg-pp-lst rp-term-listp)
                        (arg-c-lst rp-term-listp)
                        (to-be-coughed-c-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp arg-s-lst)
                                     (rp-term-listp arg-pp-lst)
                                     (rp-term-listp arg-c-lst)))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp arg-s-lst)
                                    (rp-term-listp arg-pp-lst)
                                    (rp-term-listp arg-c-lst)))
               (to-be-coughed-s-lst rp-term-listp
                                    :hyp (and (rp-term-listp arg-s-lst)
                                              (rp-term-listp arg-pp-lst)
                                              (rp-term-listp arg-c-lst)))
               (to-be-coughed-pp-lst rp-term-listp
                                     :hyp (and (rp-term-listp arg-s-lst)
                                               (rp-term-listp arg-pp-lst)
                                               (rp-term-listp arg-c-lst)))
               (res-coughed-c-lst rp-term-listp
                                  :hyp (and (rp-term-listp arg-s-lst)
                                            (rp-term-listp arg-pp-lst)
                                            (rp-term-listp arg-c-lst)
                                            (rp-term-listp to-be-coughed-c-lst))))
  :verify-guards :after-returns
  (b* (((when (atom arg-s-lst))
        (mv arg-pp-lst arg-c-lst nil nil to-be-coughed-c-lst))
       ((mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst)
        (c-of-s-fix-lst (cdr arg-s-lst)
                        arg-pp-lst
                        arg-c-lst
                        to-be-coughed-c-lst))
       (cur-s (car arg-s-lst))
       ((mv cur-s cur-s-is-negated)
        (case-match cur-s
          (('-- n)
           (mv n t))
          (& (mv cur-s nil))))
       #|((mv to-be-coughed-s-lst cur-s)
       (case-match cur-s
       (('-- n)
       (mv (s-sum-merge-aux to-be-coughed-s-lst (list cur-s)) n))
       (& (mv to-be-coughed-s-lst cur-s))))|#
       (cur-s (ex-from-rp$ cur-s)))
    (case-match cur-s
      (('s & s-arg-pp s-arg-c)
       (b* (((mv & to-be-coughed-pp-lst2 to-be-coughed-c-lst2)
             (create-c-instance nil
                                (list-to-lst s-arg-pp)
                                (list-to-lst s-arg-c)))

            ;;(to-be-coughed-c-lst2 (add-c-rp-bitp to-be-coughed-c-lst2))

            (to-be-coughed-c-lst2 (if cur-s-is-negated
                                      to-be-coughed-c-lst2
                                    (negate-lst to-be-coughed-c-lst2)))
            (to-be-coughed-pp-lst2 (if cur-s-is-negated
                                       to-be-coughed-pp-lst2
                                     (negate-lst to-be-coughed-pp-lst2)))

            (to-be-coughed-pp-lst (pp-sum-merge-aux to-be-coughed-pp-lst
                                                    to-be-coughed-pp-lst2))
            (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                  to-be-coughed-c-lst2))
            (arg-pp-lst (pp-sum-merge-aux arg-pp-lst
                                          (if cur-s-is-negated
                                              (negate-lst (list-to-lst s-arg-pp))
                                            (list-to-lst s-arg-pp))))
            (arg-c-lst (s-sum-merge-aux arg-c-lst
                                        (if cur-s-is-negated
                                            (negate-lst (list-to-lst s-arg-c))
                                          (list-to-lst s-arg-c))))
            ;; ((mv & & arg-c-lst &)
            ;;  (c-sum-merge-main arg-c-lst (list-to-lst s-arg-c)))
            )
         (mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst)))
      (''0
       (mv arg-pp-lst arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst))
      (& (progn$
          (hard-error 'c-of-s-fix-lst
                      "Unexpected single-s instance: ~p0 ~%"
                      (list (cons #\0 cur-s)))
          (mv (cons (car arg-s-lst) arg-pp-lst) arg-c-lst to-be-coughed-s-lst to-be-coughed-pp-lst to-be-coughed-c-lst))))))

(local
 (defthm rp-termp-lemma1
   (implies (and (consp x)
                 (rp-term-listp x))
            (rp-termp (car x)))))

(define s-of-s-fix-lst ((s-lst rp-term-listp)
                        (pp-lst rp-term-listp)
                        (c-lst rp-term-listp)
                        &key
                        (clean-args 'nil)
                        (limit '(expt 2 30)))
  :returns (mv (pp-res-lst)
               (c-res-lst))
  :guard (natp limit)
  :measure (nfix limit)
  :verify-guards nil
  (b* (((when (zp limit))
        (progn$ (hard-error 's-of-s-fix-lst "Limit reached!.." nil)
                (mv (append pp-lst s-lst) c-lst)))
       ((when (atom s-lst)) (mv pp-lst c-lst))
       ((mv pp-lst c-lst) (s-of-s-fix-lst (cdr s-lst) pp-lst c-lst
                                          :limit (1- limit)
                                          :clean-args clean-args))
       (cur-s (ex-from-rp/-- (car s-lst))))
    (case-match cur-s
      (('s & cur-pp cur-c)
       (b* ((cur-c-lst (list-to-lst cur-c))
            ((mv coughed-s coughed-pp-lst c-lst &)
             (c-sum-merge-main cur-c-lst c-lst
                               :auto-swap t
                               :clean-c1-lst nil
                               :cough-c-lst t
                               :clean-args-for-s clean-args))

            (pp-lst (if clean-args
                        (pp-sum-merge-lst-for-s coughed-pp-lst pp-lst)
                      (pp-sum-merge-aux coughed-pp-lst pp-lst)))
            (pp-lst (if clean-args
                        (pp-sum-merge-lst-for-s (list-to-lst cur-pp) pp-lst)
                      (pp-sum-merge-aux (list-to-lst cur-pp) pp-lst)))
            (coughed-s-lst (list-to-lst coughed-s))
            #|((unless coughed-s-lst)
            (mv pp-lst c-lst))||#
            ((mv pp-lst c-lst)
             (s-of-s-fix-lst coughed-s-lst pp-lst c-lst
                             :limit (1- limit)
                             :clean-args clean-args)))
         (mv pp-lst c-lst)))
      (''nil
       (mv pp-lst c-lst))
      (&
       (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
               (hard-error 's-of-s-fix-lst "Read above.." nil)
               (mv (cons cur-s pp-lst) c-lst)))))
  ///
  (acl2::defret
    rp-term-listp-of-<fn>
    :hyp (and (rp-term-listp s-lst)
              (rp-term-listp pp-lst)
              (rp-term-listp c-lst))
    (and (rp-term-listp c-res-lst)
         (rp-term-listp pp-res-lst)))

  (verify-guards s-of-s-fix-lst-fn))

#|(define s-of-s-fix ((s rp-termp)
(pp rp-termp)
(c-lst rp-term-listp))
:verify-guards nil
:returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
(rp-termp pp)
(rp-term-listp c-lst)))
(c-res-lst rp-term-listp :hyp (and (rp-termp s)
(rp-termp pp)
(rp-term-listp c-lst))))
(b* ((s-lst (list-to-lst s))
((when (equal s-lst nil))  (mv pp c-lst))
((mv pp-lst c-lst)
(s-of-s-fix-lst s-lst (list-to-lst pp) c-lst))
;; MAYBE clear c-lst here!
;;(pp-lst (pp-sum-merge-aux (list-to-lst pp) pp-lst))
(pp (create-list-instance pp-lst)))
(mv pp c-lst)))||#

;;;;;;;

(define c-pattern3-reduce ((s-lst rp-term-listp)
                           (pp-lst rp-term-listp)
                           (c-lst rp-term-listp)
                           (s-coughed-lst rp-term-listp)
                           (pp-coughed-lst rp-term-listp)
                           (c-coughed-lst rp-term-listp))
  :verify-guards t
  :returns (mv (res-s-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    (rp-term-listp s-coughed-lst)
                                    (rp-term-listp pp-coughed-lst)
                                    (rp-term-listp c-coughed-lst)
                                    ))
               (res-pp-lst rp-term-listp
                           :hyp (and (rp-term-listp s-lst)
                                     (rp-term-listp pp-lst)
                                     (rp-term-listp c-lst)
                                     (rp-term-listp s-coughed-lst)
                                     (rp-term-listp pp-coughed-lst)
                                     (rp-term-listp c-coughed-lst)
                                     ))
               (res-c-lst rp-term-listp
                          :hyp (and (rp-term-listp s-lst)
                                    (rp-term-listp pp-lst)
                                    (rp-term-listp c-lst)
                                    (rp-term-listp s-coughed-lst)
                                    (rp-term-listp pp-coughed-lst)
                                    (rp-term-listp c-coughed-lst)
                                    ))
               (res-s-coughed-lst rp-term-listp
                                  :hyp (and (rp-term-listp s-lst)
                                            (rp-term-listp pp-lst)
                                            (rp-term-listp c-lst)
                                            (rp-term-listp s-coughed-lst)
                                            (rp-term-listp pp-coughed-lst)
                                            (rp-term-listp c-coughed-lst)
                                            ))
               (res-pp-coughed-lst rp-term-listp
                                   :hyp (and (rp-term-listp s-lst)
                                             (rp-term-listp pp-lst)
                                             (rp-term-listp c-lst)
                                             (rp-term-listp s-coughed-lst)
                                             (rp-term-listp pp-coughed-lst)
                                             (rp-term-listp c-coughed-lst)
                                             ))
               (res-c-coughed-lst rp-term-listp
                                  :hyp (and (rp-term-listp s-lst)
                                            (rp-term-listp pp-lst)
                                            (rp-term-listp c-lst)
                                            (rp-term-listp s-coughed-lst)
                                            (rp-term-listp pp-coughed-lst)
                                            (rp-term-listp c-coughed-lst)
                                            )))

  (b* (((when (or (not (pattern3-reduce-enabled))
                  (not (odd-many-ones pp-lst))))
        (mv s-lst pp-lst c-lst s-coughed-lst pp-coughed-lst c-coughed-lst))

       (res-s-lst s-lst)
       (res-pp-lst (cdr pp-lst))
       (res-c-lst c-lst)

       ((mv new-pp-lst new-c-lst)
        (s-of-s-fix-lst s-lst
                        (cdr pp-lst)
                        c-lst))

       #| (- (and (not-well-merged-c-lst new-c-lst)
       (hard-error 'c-pattern3-reduce
       "Mergable c-lst ~p0 ~%"
       (list (cons #\0 new-c-lst)))))||#

       ((mv res-s-lst2 res-pp-lst2 res-c-lst2)
        (create-s-instance (create-list-instance new-pp-lst)
                           (create-list-instance new-c-lst)))

       (res-s-coughed-lst (s-sum-merge-aux s-coughed-lst res-s-lst2))
       (res-pp-coughed-lst (pp-sum-merge-aux pp-coughed-lst res-pp-lst2))
       (res-c-coughed-lst (s-sum-merge-aux c-coughed-lst res-c-lst2)))
    (mv res-s-lst res-pp-lst res-c-lst
        res-s-coughed-lst res-pp-coughed-lst res-c-coughed-lst)))

;;;;;;;;;

(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

(local
 (defthm rp-term-listp-of-repeat
   (implies (rp-termp x)
            (rp-term-listp (repeat num x)))
   :hints (("Goal"
            :induct (REPEAT NUM X)
            :in-theory (e/d (rp-term-listp repeat) ())))))

;;;;;;;;;;;;;;;;;;;
(progn
  (define recollectable-pp-p ((pp))
    (b* ((pp (ex-from--- pp))
         (pp (ex-from-rp pp)))
      (case-match pp
        (('and-list & ('list a1 a2 a3 a4))
         (b* ((a1 (ex-from-rp a1))
              (a2 (ex-from-rp a2))
              (a3 (ex-from-rp a3))
              (a4 (ex-from-rp a4))
              (a1 (ex-from-rp (case-match a1 (('logbit$inline & x) x) (& a1))))
              (a2 (ex-from-rp (case-match a2 (('logbit$inline & x) x) (& a2))))
              (a3 (ex-from-rp (case-match a3 (('logbit$inline & x) x) (& a3))))
              (a4 (ex-from-rp (case-match a4 (('logbit$inline & x) x) (& a4)))))
           (or (and (equal a1 a2)
                    (equal a1 a3)
                    (not (equal a1 a4))
                    1)
               (and (equal a4 a2)
                    (equal a4 a3)
                    (not (equal a1 a4))
                    2)))))))

  (define recollect-pp ((pp rp-termp))
    :guard (recollectable-pp-p pp)
    :prepwork ((local
                (defthm is-rp-of-rp-bitp
                  (is-rp `(rp 'bitp ,x))
                  :hints (("Goal"
                           :in-theory (e/d (is-rp) ()))))))
    :returns (mv  (res-pp-lst rp-term-listp :hyp (rp-termp pp))
                  (c rp-termp :hyp (rp-termp pp)))
    (b* ((p (recollectable-pp-p pp))
         (pp-orig pp)
         ((mv pp negated) (case-match pp (('-- x) (mv x t)) (& (mv pp nil))))
         (pp (ex-from-rp pp))
         ((mv pp1 pp2 pp3 pp4 pp5 pp6 valid)
          (case-match pp
            (('and-list & ('list a1 a2 a3 a4))
             (cond ((equal p 1)
                    (mv (create-and-list-instance (list a1 a4))
                        (create-and-list-instance (list a2 a4))
                        (create-and-list-instance (list a3 a4))
                        (create-and-list-instance (list a1 a2 a4))
                        (create-and-list-instance (list a1 a3 a4))
                        (create-and-list-instance (list a2 a3 a4))
                        t))
                   ((equal p 2)
                    (mv (create-and-list-instance (list a1 a2))
                        (create-and-list-instance (list a1 a3))
                        (create-and-list-instance (list a1 a4))
                        (create-and-list-instance (list a1 a2 a3))
                        (create-and-list-instance (list a1 a2 a4))
                        (create-and-list-instance (list a1 a3 a4))
                        t))
                   (t (mv ''0 ''0 ''0 ''0 ''0 ''0 nil))))
            (& (mv ''0 ''0 ''0 ''0 ''0 ''0 nil))))
         ((unless valid) (mv (list pp-orig pp-orig) ''0))
         (c (b* ((pp-lst (pp-sum-merge-aux (list pp1)
                                           (pp-sum-merge-aux (list pp2)
                                                             (list pp3))))
                 (pp (create-list-instance pp-lst))
                 (hash-code (calculate-c-hash ''nil pp ''nil))
                 (c `(rp 'bitp (c ',hash-code 'nil ,pp 'nil )))
                 (c (if negated c `(-- ,c))))
              c))
         ((mv pp4 pp5 pp6)
          (if negated
              (mv `(-- ,pp4) `(-- ,pp5) `(-- ,pp6))
            (mv pp4 pp5 pp6)))
         (res-pp-lst (pp-sum-merge-aux (list pp4)
                                       (pp-sum-merge-aux (list pp5) (list
                                                                     pp6)))))
      (mv res-pp-lst c)))

  (define recollect-pp-lst-to-sc ((pp-lst rp-term-listp))

    :measure (cons-count pp-lst)
    :prepwork ((local
                (defthm cons-count-cddr
                  (implies (and (consp pp-lst)
                                (consp (cdr pp-lst)))
                           (o< (cons-count (cddr pp-lst))
                               (cons-count pp-lst)))
                  :hints (("Goal"
                           :induct (cons-count pp-lst)
                           :do-not-induct t
                           :in-theory (e/d (cons-count)
                                           (+-IS-SUM))))))
               (local
                (in-theory (enable measure-lemmas))))
    :verify-guards :after-returns
    :returns (mv (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
                 (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
    (cond ((atom pp-lst) (mv pp-lst nil))
          ((atom (cdr pp-lst)) (mv pp-lst nil))
          ((and (equal (car pp-lst)
                       (cadr pp-lst))
                (recollectable-pp-p (car pp-lst)))
           (b* (((mv new-pp-lst c)
                 (recollect-pp (car pp-lst)))
                ((mv rest-pp-lst rest-c-lst)
                 (recollect-pp-lst-to-sc (cddr pp-lst))))
             (mv (pp-sum-merge-aux rest-pp-lst new-pp-lst)
                 (s-sum-merge-aux (list c) rest-c-lst))))
          (t (b* (((mv rest-pp-lst rest-c-lst)
                   (recollect-pp-lst-to-sc (cdr pp-lst)))
                  (can-be-consed (or (atom rest-pp-lst)
                                     (b* (((mv order &) (pp-order (car pp-lst)
                                                                  (car rest-pp-lst))))
                                       order))))
               (mv (if can-be-consed
                       (cons-with-hint (car pp-lst) rest-pp-lst pp-lst)
                     (pp-sum-merge-aux (list (car pp-lst)) rest-pp-lst))
                   rest-c-lst)))))

  (progn
    (encapsulate
      (((recollect-pp-enabled) => *))
      (local
       (defun recollect-pp-enabled ()
         nil)))

    (defmacro enable-recollect-pp (enable)
      (if enable
          `(defattach recollect-pp-enabled return-t)
        `(defattach recollect-pp-enabled return-nil)))

    (enable-recollect-pp nil))

  (define recollect-pp-lst-to-sc-main ((pp-lst rp-term-listp))
    :returns (mv (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
                 (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
    :enabled t
    (if (recollect-pp-enabled)
        (recollect-pp-lst-to-sc pp-lst)
      (mv pp-lst nil))))

;;;;;;;;;;;;;;;;;;
;; cross product applicable pp
;;:i-am-here

(progn
  (encapsulate
    (((cross-product-two-larges-enabled) => *))
    (local
     (defun cross-product-two-larges-enabled ()
       nil)))

  (defmacro enable-cross-product-two-larges (enable)
    (if enable
        `(defattach cross-product-two-larges-enabled return-t)
      `(defattach cross-product-two-larges-enabled return-nil)))

  (enable-cross-product-two-larges nil))

(define cross-product-pp-pattern-check-aux ((ppe-lst rp-term-listp))
  :returns (mv (pass booleanp)
               (s/c-found booleanp))
  (if (atom ppe-lst)
      (mv t nil)
    (b* ((cur-orig (car ppe-lst))
         (has-bitp (has-bitp-rp cur-orig))
         (cur (ex-from-rp cur-orig)))
      (case-match cur
        (('logbit$inline & &)
         (cross-product-pp-pattern-check-aux (cdr ppe-lst)))
        (('s & & &)
         (b* (((mv rest-valid rest-s/c-found)
               (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
           (mv (and rest-valid
                    ;;(equal (len (acl2::all-vars cur)) 1)
                    (not rest-s/c-found))
               t)))
        (('c & & & &)
         (b* (((mv rest-valid rest-s/c-found)
               (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
           (mv (and rest-valid
                    ;;(equal (len (acl2::all-vars cur)) 1)
                    (not rest-s/c-found)
                    has-bitp)
               t)))
        (('s-c-res & & &)
         (b* (((mv rest-valid rest-s/c-found)
               (cross-product-pp-pattern-check-aux (cdr ppe-lst))))
           (mv (and rest-valid
                    (not rest-s/c-found)
                    has-bitp)
               t)))
        (& (mv nil nil))))))

(define cross-product-pp-pattern-check ((single-pp rp-termp))
  :returns (pass booleanp)
  (case-match single-pp
    (('and-list & ('list . lst))
     (b* (((mv pass s/c-found)
           (cross-product-pp-pattern-check-aux lst)))
       (and pass s/c-found)))
    (& nil)))

(define cross-product-pp-pattern-check2-aux ((term rp-termp))
  :returns (mv (pass booleanp)
               (s/c-count natp))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :verify-guards :after-returns
  (b* ((has-bitp (has-bitp-rp term))
       (term (ex-from-rp term)))
    (cond ((binary-?-p term)
           (b* (((mv pass1 s/c-count1)
                 (cross-product-pp-pattern-check2-aux (cadr term)))
                ((mv pass2 s/c-count2)
                 (cross-product-pp-pattern-check2-aux (caddr term)))
                ((mv pass3 s/c-count3)
                 (cross-product-pp-pattern-check2-aux (cadddr term)))
                (sum13 (+ s/c-count1 s/c-count3)))
             (mv (and pass1 pass2 pass3
                      (equal sum13 0))
                 (+ sum13 s/c-count2))))
          ((binary-and-p term)
           (b* (((mv pass1 s/c-count1)
                 (cross-product-pp-pattern-check2-aux (cadr term)))
                ((mv pass2 s/c-count2)
                 (cross-product-pp-pattern-check2-aux (caddr term))))
             (mv (and pass1 pass2 )
                 (+ s/c-count1 s/c-count2))))
          ((or (binary-or-p term)
               (binary-xor-p term))
           (b* (((mv pass1 s/c-count1)
                 (cross-product-pp-pattern-check2-aux (cadr term)))
                ((mv pass2 s/c-count2)
                 (cross-product-pp-pattern-check2-aux (caddr term)))
                (total (+ s/c-count1 s/c-count2)))
             (mv (and pass1 pass2 (equal total 0))
                 total)))
          ((binary-not-p term)
           (b* (((mv pass s/c-count)
                 (cross-product-pp-pattern-check2-aux (cadr term))))
             (mv (and pass (equal s/c-count 0)) s/c-count)))
          ((logbit-p term)
           (mv t 0))
          ((single-s-p term)
           (mv t 1))
          ((single-c-p term)
           (mv has-bitp 1))
          ((single-s-c-res-p term)
           (mv has-bitp 1))
          (t (mv has-bitp 0)))))

(define cross-product-pp-pattern-check2 ((single-pp rp-termp))
  :returns (pass booleanp)
  (b* (((mv pass s/c-count)
        (cross-product-pp-pattern-check2-aux single-pp)))
    (and pass
         (equal s/c-count 1))))

(define cross-product-pp-pattern-check3 ((single-pp rp-termp))
  (case-match single-pp
    (('and-list & ('list x y))
     (or (and (single-s-p (ex-from-rp$ x))
              (single-s-p (ex-from-rp$ y)))
         (and (single-c-p (ex-from-rp$ x))
              (has-bitp-rp x)
              (single-s-p (ex-from-rp$ y)))
         (and (single-s-p (ex-from-rp$ x))
              (single-c-p (ex-from-rp$ y))
              (has-bitp-rp y))
         (and (single-s-p (ex-from-rp$ x))
              (single-s-c-res-p (ex-from-rp$ y))
              (has-bitp-rp y)))))
  ///
  (defthm cross-product-pp-pattern-check3-implies-fc
    (implies (cross-product-pp-pattern-check3 single-pp)
             (case-match single-pp
               (('and-list & ('list & &)) t)))
    :rule-classes :forward-chaining))

(define cross-product-pp-aux-precollect ((e-lst rp-term-listp))
  :returns (mv (single-s/c rp-termp :hyp (rp-term-listp e-lst))
               (res-e-lst rp-term-listp :hyp (rp-term-listp e-lst))
               (valid booleanp))
  (if (atom e-lst)
      (mv ''1 nil t)
    (b* ((cur-orig (car e-lst))
         (has-bitp (has-bitp-rp cur-orig))
         (cur (ex-from-rp cur-orig))
         ((mv rest-single-s/c rest-lst valid)
          (cross-product-pp-aux-precollect (cdr e-lst)))
         ((unless (and valid
                       #|(equal rest-single-s/c ''1)|#))
          (mv rest-single-s/c ;; should never come here becasue of pattern-check
              (cons cur rest-lst)
              nil)))
      (case-match cur
        (('logbit$inline & &)
         (mv rest-single-s/c
             (cons-with-hint cur rest-lst e-lst)
             t))
        (('s & & &)
         (if (equal rest-single-s/c ''1)
             (mv cur-orig (cdr e-lst) t)
           (mv ''1 nil nil)))
        (('c & & & &)
         (if (equal rest-single-s/c ''1)
             (mv cur-orig (cdr e-lst) has-bitp)
           (mv ''1 nil nil)))
        (('s-c-res & & &)
         (if (equal rest-single-s/c ''1)
             (mv cur-orig (cdr e-lst) has-bitp)
           (mv ''1 nil nil)))
        (&  ;; should never come here because of pattern-check
         (mv rest-single-s/c
             (cons cur rest-lst)
             nil))))))

(define cross-product-pp-aux-precollect2-aux ((single-pp rp-termp)
                                              (side-pp-lst rp-term-listp))
  :returns (res-side-pp-lst rp-term-listp :hyp (and (rp-termp single-pp)
                                                    (rp-term-listp side-pp-lst)))
  (if (atom side-pp-lst)
      nil
    (cons `(binary-and ,single-pp
                       ,(car side-pp-lst))
          (cross-product-pp-aux-precollect2-aux single-pp (cdr side-pp-lst)))))

(define cross-product-pp-aux-precollect2 ((single-pp rp-termp))
  :returns (mv (single-s/c rp-termp :hyp (rp-termp single-pp))
               (res-pp rp-termp :hyp (rp-termp single-pp))
               (side-pp-lst rp-term-listp :hyp (rp-termp single-pp))
               (valid booleanp))
  :measure (cons-count single-pp)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :verify-guards :after-returns
  (b* ((has-bitp (has-bitp-rp single-pp))
       (term (ex-from-rp single-pp)))
    (cond ((binary-?-p term)
           (b* ((test (cadr term))
                (then (caddr term))
                (else (cadddr term))
                ((mv s/c1 pp1 side-pp1 valid)
                 (cross-product-pp-aux-precollect2 then))
                ((when (equal s/c1 ''1))
                 (mv ''1 single-pp nil t))
                ((unless valid)
                 (mv ''nil ''nil nil nil)))
             (mv s/c1
                 `(binary-and ,test ,pp1)
                 (cons `(binary-and (binary-not ,test) ,else)
                       (cross-product-pp-aux-precollect2-aux test side-pp1))
                 t)))
          ((or (binary-not-p term)
               (binary-or-p term)
               (binary-xor-p term)
               (logbit-p term)
               (equal term ''1)
               (equal term ''0))
           (mv ''1 single-pp nil t))
          ((binary-and-p term)
           (b* (((mv s/c1 pp1 side1 valid1)
                 (cross-product-pp-aux-precollect2 (cadr term)))
                ((mv s/c2 pp2 side2 valid2)
                 (cross-product-pp-aux-precollect2 (caddr term)))
                ((unless (and valid1 valid2))
                 (mv ''nil ''nil nil nil))
                (s/c1-e (not (equal s/c1 ''1)))
                (s/c2-e (not (equal s/c2 ''1)))
                ((when (and s/c1-e (not s/c2-e) (not side2)))
                 (mv s/c1 `(binary-and ,pp1 ,pp2)
                     (cross-product-pp-aux-precollect2-aux pp2 side1)
                     t))
                ((when (and s/c2-e (not s/c1-e) (not side1)))
                 (mv s/c2 `(binary-and ,pp1 ,pp2)
                     (cross-product-pp-aux-precollect2-aux pp1 side2)
                     t))
                ((when (and (not s/c1-e) (not s/c2-e) (not side1) (not side2)))
                 (mv ''1 `(binary-and ,pp1 ,pp2) nil t)))
             (mv ''nil ''nil nil nil)))
          ((single-s-p term)
           (mv single-pp ''1 nil t))
          ((or (single-c-p term)
               (single-s-c-res-p term))
           (mv single-pp ''1 nil has-bitp))
          (t
           (mv ''1 single-pp nil has-bitp)))))

(define and-list-to-binary-and-aux (lst)
  :returns (res rp-termp :hyp (rp-term-listp lst))
  (if (atom lst)
      ''1
    (if (atom (cdr lst))
        `(binary-and ,(car lst) '1)
      (if (atom (cddr lst))
          `(binary-and ,(car lst) ,(cadr lst))
        `(binary-and ,(car lst)
                     ,(and-list-to-binary-and-aux (cdr lst)))))))

(define and-list-to-binary-and ((term rp-termp))
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (valid booleanp))
  (case-match term
    (('and-list & ''nil)
     (mv ''1 t))
    (('and-list & ('list . lst))
     (mv (and-list-to-binary-and-aux lst) t))
    (('logbit$inline & &)
     (mv term t))
    (& (mv term (or (binary-fnc-p term)
                    (equal term ''1)
                    (equal term ''0)
                    (has-bitp-rp term))))))

(define cross-product-pp-aux-for-pp-lst-aux ((pp-lst rp-term-listp)
                                             (e-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                   (rp-term-listp e-lst)))
               (valid booleanp))
  (if (atom pp-lst)
      (mv nil t)
    (b* ((cur (car pp-lst))
         ((mv cur cur-is-signed)
          (case-match cur (('-- e) (mv e t)) (& (mv cur nil)))))
      (cond
       ((and (consp e-lst)
             (not (cdr e-lst))
             (binary-fnc-p (car e-lst)))
        (b* (((mv cur-in-binary-fnc cur-is-bitp) (and-list-to-binary-and cur))
             ((Unless cur-is-bitp) (mv nil nil))
             ((mv rest-pp-lst valid)
              (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst))
             (res `(binary-and ,cur-in-binary-fnc ,(car e-lst))))
          (mv (cons (if cur-is-signed `(-- ,res) res)
                    rest-pp-lst)
              valid)))
       ((and-list-p cur)
        (case-match cur
          (('and-list & ('list . lst))
           (b* ((res-e-lst (merge-sorted-and$-lists lst e-lst))
                (cur-pp (create-and-list-instance res-e-lst))
                (cur-pp (if cur-is-signed `(-- ,cur-pp) cur-pp))
                ((mv rest-pp-lst valid)
                 (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst)))
             (mv (cons cur-pp rest-pp-lst)
                 valid)))
          (&
           (mv nil (hard-error 'cross-product-pp-aux-for-pp-lst-aux
                               "Unexpected pp-lst element: ~p0 ~%"
                               (list (cons #\0 cur)))))))
       ((or (logbit-p cur)
            (equal cur ''1)
            (has-bitp-rp cur))
        (b* ((res-e-lst (merge-sorted-and$-lists (list cur) e-lst))
             (cur-pp (create-and-list-instance res-e-lst))
             (cur-pp (if cur-is-signed `(-- ,cur-pp) cur-pp))
             ((mv rest-pp-lst valid)
              (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst)))
          (mv (cons cur-pp rest-pp-lst)
              valid)))
       ((binary-fnc-p cur)
        (b* ((e-lst-in-binary-fnc (and-list-to-binary-and-aux e-lst))
             ((mv rest-pp-lst valid)
              (cross-product-pp-aux-for-pp-lst-aux (cdr pp-lst) e-lst))
             (res `(binary-and ,e-lst-in-binary-fnc ,cur)))
          (mv (cons (if cur-is-signed `(-- ,res) res)
                    rest-pp-lst)
              valid)))
       (t (mv nil (hard-error 'cross-product-pp-aux-for-pp-lst-aux
                              "Unexpected pp-lst element: ~p0 ~%"
                              (list (cons #\0 cur)))))))))

(define cross-product-pp-aux-for-pp-lst  ((pp-lst rp-term-listp)
                                          (e-lst rp-term-listp))
  :returns (mv (res-pp-lst rp-term-listp :hyp (and (rp-term-listp pp-lst)
                                                   (rp-term-listp e-lst)))
               (valid booleanp))
  (b* (((mv res-pp-lst valid)
        (cross-product-pp-aux-for-pp-lst-aux pp-lst e-lst))
       ((unless valid)
        (mv res-pp-lst valid))
       ((when (pp-lst-orderedp res-pp-lst))
        (mv res-pp-lst valid))
       (res-pp-lst (pp-sum-sort-lst res-pp-lst)))
    (mv res-pp-lst valid)))

(define cross-product-pp-aux-for-s/c ((single-s/c rp-termp)
                                      (e-lst rp-term-listp))
  :verify-guards nil
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  :measure (cons-count single-s/c)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork ((local
              (defthm m-lemma1
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CADDDR x)))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CADDDR x)))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))
             (local
              (defthm m-lemma2
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))

             )

  (b* (((mv single-s/c negated)
        (if (--.p single-s/c) (mv (cadr single-s/c) t) (mv single-s/c nil)))
       (single-s/c (ex-from-rp$ single-s/c)))
    (cond ((single-s-p single-s/c)
           (case-match single-s/c
             (('s & pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv new-pp-lst valid)
                    (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                   ((unless valid) (mv nil nil nil nil))
                   ((mv rest-s-lst rest-pp-lst rest-c-lst valid)
                    (cross-product-pp-aux-for-s/c single-c e-lst))
                   ((unless (and valid
                                 (equal rest-s-lst nil)))
                    (mv nil nil nil nil))
                   (new-pp-lst (pp-sum-merge-aux rest-pp-lst new-pp-lst))
                   (new-pp-lst (s-fix-pp-args-aux new-pp-lst))
                   (rest-c-lst (s-fix-pp-args-aux rest-c-lst))
                   ((mv res-s-lst res-pp-lst res-c-lst)
                    (create-s-instance (create-list-instance new-pp-lst)
                                       (create-list-instance rest-c-lst))))
                (mv (negate-lst res-s-lst negated)
                    (negate-lst res-pp-lst negated)
                    (negate-lst res-c-lst negated)
                    t)))
             (('s & ('list . pp-lst) ''nil)
              (b* (((mv new-pp-lst valid)
                    (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                   ((unless valid) (mv nil nil nil nil))
                   (new-pp-lst (s-fix-pp-args-aux new-pp-lst))
                   ((mv res-s-lst res-pp-lst res-c-lst)
                    (create-s-instance (create-list-instance new-pp-lst)
                                       ''nil)))
                (mv (negate-lst res-s-lst negated)
                    (negate-lst res-pp-lst negated)
                    (negate-lst res-c-lst negated)
                    t)))
             (& (mv nil nil nil nil))))
          ((single-c-p single-s/c)
           (case-match single-s/c
             (('c & ''nil pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv new-pp-lst valid)
                    (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                   ((unless valid) (mv nil nil nil nil))
                   ((mv rest-s-lst rest-pp-lst rest-c-lst valid)
                    (cross-product-pp-aux-for-s/c single-c e-lst))
                   ((unless (and valid
                                 (equal rest-s-lst nil)))
                    (mv nil nil nil nil))
                   (new-pp-lst (pp-sum-merge-aux rest-pp-lst new-pp-lst))
                   ((mv coughed-pp-lst new-pp-lst) (c-fix-arg-aux new-pp-lst t))
                   ((mv coughed-c-lst rest-c-lst) (c-fix-arg-aux rest-c-lst t))
                   ((mv res-s-lst res-pp-lst res-c-lst)
                    (create-c-instance nil
                                       new-pp-lst
                                       rest-c-lst))
                   (res-pp-lst (pp-sum-merge-aux coughed-pp-lst res-pp-lst))
                   (res-c-lst (s-sum-merge-aux res-c-lst coughed-c-lst)))
                (mv (negate-lst res-s-lst negated)
                    (negate-lst res-pp-lst negated)
                    (negate-lst res-c-lst negated)
                    t)))
             (('c & ''nil ('list . pp-lst) ''nil)
              (b* (((mv new-pp-lst valid)
                    (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                   ((unless valid) (mv nil nil nil nil))
                   ((mv coughed-pp-lst new-pp-lst) (c-fix-arg-aux new-pp-lst t))
                   ((mv res-s-lst res-pp-lst res-c-lst)
                    (create-c-instance nil
                                       new-pp-lst
                                       nil))
                   (res-pp-lst (pp-sum-merge-aux coughed-pp-lst res-pp-lst)))
                (mv (negate-lst res-s-lst negated)
                    (negate-lst res-pp-lst negated)
                    (negate-lst res-c-lst negated)
                    t)))
             (& (mv nil nil nil nil))))
          (t (mv nil nil nil nil))))

  ///

  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c)
                  (rp-term-listp e-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst))))

  (verify-guards cross-product-pp-aux-for-s/c))

(define cross-product-pp-aux-for-s/c-lst ((s/c-lst rp-term-listp)
                                          (e-lst rp-term-listp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  :verify-guards nil
  (if (atom s/c-lst)
      (mv nil nil nil t)
    (b* (((mv res-s-lst res-pp-lst res-c-lst valid)
          (cross-product-pp-aux-for-s/c (car s/c-lst) e-lst))
         ((unless valid) (mv nil nil nil nil))
         ((mv res-s-lst2 res-pp-lst2 res-c-lst2 valid)
          (cross-product-pp-aux-for-s/c-lst (cdr s/c-lst) e-lst))
         ((unless valid) (mv nil nil nil nil)))
      (mv (s-sum-merge-aux res-s-lst res-s-lst2)
          (pp-sum-merge-aux res-pp-lst res-pp-lst2)
          (s-sum-merge-aux res-c-lst res-c-lst2)
          t)))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (and (rp-term-listp s/c-lst)
                  (rp-term-listp e-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst))))
  (verify-guards cross-product-pp-aux-for-s/c-lst))

(define cross-product-pp-aux-for-s/c-main ((single-s/c rp-termp)
                                           (e-lst rp-term-listp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  (b* ((single-s/c-orig single-s/c)
       (single-s/c (ex-from-rp$ single-s/c)))
    (cond ((single-s-c-res-p single-s/c)
           (b* ((s-lst (list-to-lst (cadr single-s/c)))
                (pp-lst (list-to-lst (caddr single-s/c)))
                (c-lst (list-to-lst (cadddr single-s/c)))
                ((mv res-s-lst1 res-pp-lst1 res-c-lst1 valid)
                 (cross-product-pp-aux-for-s/c-lst s-lst e-lst))
                ((unless valid) (mv nil nil nil nil))
                ((mv res-pp-lst2 valid)
                 (cross-product-pp-aux-for-pp-lst pp-lst e-lst))
                ((unless valid) (mv nil nil nil nil))
                ((mv res-s-lst3 res-pp-lst3 res-c-lst3 valid)
                 (cross-product-pp-aux-for-s/c-lst c-lst e-lst))
                ((unless valid) (mv nil nil nil nil)))
             (mv (s-sum-merge-aux res-s-lst1 res-s-lst3)
                 (pp-sum-merge-aux res-pp-lst1
                                   (pp-sum-merge-aux res-pp-lst2 res-pp-lst3))
                 (s-sum-merge-aux res-c-lst1 res-c-lst3)
                 t)))
          (t (cross-product-pp-aux-for-s/c single-s/c-orig e-lst))))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c)
                  (rp-term-listp e-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst)))))

(define cross-product-two-larges-aux-pp-lst ((pp-lst rp-term-listp)
                                             (single-s/c2 rp-termp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  (if (atom pp-lst)
      (mv nil nil nil t)
    (b* (((mv rest-s-lst rest-pp-lst rest-c-lst valid)
          (cross-product-two-larges-aux-pp-lst (cdr pp-lst) single-s/c2))
         ((unless valid)
          (mv nil nil nil nil))
         (cur-pp (car pp-lst))
         ((mv cur-s-lst cur-pp-lst cur-c-lst valid)
          (case-match cur-pp
            (('and-list & ('list . e-lst))
             (cross-product-pp-aux-for-s/c-main single-s/c2 e-lst))
            (('binary-and x y)
             (cross-product-pp-aux-for-s/c-main single-s/c2 (list x y)))
            (('logbit$inline & &)
             (cross-product-pp-aux-for-s/c-main single-s/c2 (list cur-pp)))
            (''1
             (cond ((single-s-p (ex-from-rp$ single-s/c2))
                    (mv (list single-s/c2) nil nil t))
                   ((single-c-p (ex-from-rp$ single-s/c2))
                    (mv nil nil (list single-s/c2) t))
                   (t
                    (cross-product-pp-aux-for-s/c-main single-s/c2 (list ''1)))))
            (& (mv nil nil nil nil))))
         ((unless valid)
          (mv nil nil nil nil)))
      (mv (s-sum-merge-aux rest-s-lst cur-s-lst)
          (pp-sum-merge-aux rest-pp-lst cur-pp-lst)
          (s-sum-merge-aux rest-c-lst cur-c-lst)
          t)))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c2)
                  (rp-term-listp pp-lst))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst)))))

(define cross-product-two-larges-aux ((single-s/c1 rp-termp)
                                      (single-s/c2 rp-termp))
  :returns (mv (res-s-lst)
               (res-pp-lst)
               (res-c-lst)
               (valid booleanp))
  ;;:mode :program
  :measure (cons-count single-s/c1)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork ((local
              (defthm m-lemma1
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CADDDR x)))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CADDDR x)))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))
             (local
              (defthm m-lemma2
                (IMPLIES (and (consp y)
                              (<= (cons-count x) (cons-count y)))
                         (and (O< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                  (CONS-COUNT y))
                              (< (CONS-COUNT (CADR (CAR (CDDDDR x))))
                                 (CONS-COUNT y))))
                :hints (("Goal"
                         :in-theory (e/d (CONS-COUNT) ())))))

             )
  :verify-guards nil

  (b* ((?orig single-s/c1)
       (single-s/c1 (ex-from-rp$ single-s/c1)))
    (cond ((single-s-p single-s/c1)
           (case-match single-s/c1
             (('s & pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst1 pp-lst1 c-lst1 valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   ((mv s-lst2 pp-lst2 c-lst2 valid)
                    (cross-product-two-larges-aux single-c single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-sum-merge-aux s-lst1 s-lst2))
                   (s-lst (s-fix-pp-args-aux s-lst))
                   (pp-lst (pp-sum-merge-lst-for-s pp-lst1 pp-lst2))
                   (pp-lst (s-fix-pp-args-aux pp-lst))
                   (c-lst (s-sum-merge-aux c-lst1 c-lst2))
                   (c-lst (s-fix-pp-args-aux c-lst))

                   ((mv pp-lst c-lst)
                    (s-of-s-fix-lst s-lst pp-lst c-lst
                                    :clean-args t))
                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-s-instance (create-list-instance pp-lst)
                                       (create-list-instance c-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (('s & pp ''nil)
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst pp-lst c-lst valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-fix-pp-args-aux s-lst))
                   (c-lst (s-fix-pp-args-aux c-lst))
                   (pp-lst (s-fix-pp-args-aux pp-lst))

                   ((mv pp-lst c-lst)
                    (s-of-s-fix-lst s-lst pp-lst c-lst
                                    :clean-args t))
                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-s-instance (create-list-instance pp-lst)
                                       (create-list-instance c-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (& (mv nil nil nil nil))))
          ((single-c-p single-s/c1)
           (case-match single-s/c1
             (('c & ''nil pp ('list single-c))
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst1 pp-lst1 c-lst1 valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   ((mv s-lst2 pp-lst2 c-lst2 valid)
                    (cross-product-two-larges-aux single-c single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))
                   (s-lst (s-sum-merge-aux s-lst1 s-lst2))
                   (pp-lst (pp-sum-merge-aux pp-lst1 pp-lst2))
                   (c-lst (s-sum-merge-aux c-lst1 c-lst2))

                   ((mv pp-res-lst c-res-lst
                        coughed-s-lst coughed-pp-lst coughed-c-lst)
                    (c-of-s-fix-lst s-lst pp-lst c-lst nil))

                   ((mv coughed-pp-lst2 pp-res-lst)
                    (c-fix-arg-aux pp-res-lst t))
                   ((mv coughed-c-lst2 c-res-lst)
                    (c-fix-arg-aux c-res-lst t))

                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-c-instance nil pp-res-lst c-res-lst))

                   (s-res-lst (s-sum-merge-aux coughed-s-lst
                                               s-res-lst))
                   (pp-res-lst (pp-sum-merge-aux coughed-pp-lst
                                                 (pp-sum-merge-aux coughed-pp-lst2
                                                                   pp-res-lst)))
                   (c-res-lst (s-sum-merge-aux coughed-c-lst
                                               (s-sum-merge-aux coughed-c-lst2
                                                                c-res-lst))))
                (mv s-res-lst pp-res-lst c-res-lst t)))
             (('c & ''nil pp ''nil)
              (b* ((pp-lst (list-to-lst pp))
                   ((mv s-lst pp-lst c-lst valid)
                    (cross-product-two-larges-aux-pp-lst pp-lst single-s/c2))
                   ((unless valid)
                    (mv nil nil nil nil))

                   ((mv pp-res-lst c-res-lst
                        coughed-s-lst coughed-pp-lst coughed-c-lst)
                    (c-of-s-fix-lst s-lst pp-lst c-lst nil))

                   ((mv coughed-pp-lst2 pp-res-lst)
                    (c-fix-arg-aux pp-res-lst t))
                   ((mv coughed-s-lst2 c-res-lst)
                    (c-fix-arg-aux c-res-lst t))

                   ((mv s-res-lst pp-res-lst c-res-lst)
                    (create-c-instance nil pp-res-lst c-res-lst))

                   (s-res-lst (s-sum-merge-aux coughed-s-lst
                                               (s-sum-merge-aux coughed-s-lst2
                                                                s-res-lst)))
                   (pp-res-lst (pp-sum-merge-aux coughed-pp-lst
                                                 (pp-sum-merge-aux coughed-pp-lst2
                                                                   pp-res-lst)))
                   (c-res-lst (s-sum-merge-aux coughed-c-lst
                                               c-res-lst)))
                (mv s-res-lst pp-res-lst c-res-lst t)))

             (& (mv nil nil nil nil))))
          (t (mv nil nil nil nil))))
  ///

  (defret rp-term-listp-of-<fn>
    (implies (and (rp-termp single-s/c1)
                  (rp-termp single-s/c2))
             (and (rp-term-listp res-s-lst)
                  (rp-term-listp res-pp-lst)
                  (rp-term-listp res-c-lst))))

  (verify-guards cross-product-two-larges-aux))

(define cross-product-pp-aux ((single-pp rp-termp))
  :returns (mv (res-s-lst  rp-term-listp :hyp (rp-termp single-pp))
               (res-pp-lst rp-term-listp :hyp (rp-termp single-pp))
               (res-c-lst  rp-term-listp :hyp (rp-termp single-pp))
               (valid booleanp))

  (b* (((mv single-pp negated) (case-match single-pp
                                 (('-- in) (mv in t))
                                 (& (mv single-pp nil)))))
    (cond
     ((and* (and-list-p single-pp)
            ;; when there's only one s, c, or s-c-res in single-pp:
            (cross-product-pp-pattern-check single-pp))
      (b* ((e-lst (list-to-lst (caddr single-pp)))
           ((mv single-s e-lst valid)
            (cross-product-pp-aux-precollect e-lst))
           ((unless valid)
            (mv nil nil nil nil))
           ((mv res-s-lst res-pp-lst res-c-lst valid)
            (cross-product-pp-aux-for-s/c-main single-s e-lst)))
        (if negated
            (mv (negate-lst res-s-lst)
                (negate-lst res-pp-lst)
                (negate-lst res-c-lst)
                valid)
          (mv res-s-lst res-pp-lst res-c-lst valid))))
     ((and* (binary-fnc-p single-pp)
            (cross-product-pp-pattern-check2 single-pp))
      (b* (((mv single-s/c res-pp side-pp-lst valid)
            (cross-product-pp-aux-precollect2 single-pp))
           ((unless valid)
            (mv nil nil nil nil))
           ((mv res-s-lst res-pp-lst res-c-lst valid)
            (cross-product-pp-aux-for-s/c-main single-s/c (list res-pp)))
           (res-pp-lst (pp-sum-merge-aux res-pp-lst side-pp-lst)))
        (if negated
            (mv (negate-lst res-s-lst)
                (negate-lst res-pp-lst)
                (negate-lst res-c-lst)
                valid)
          (mv res-s-lst res-pp-lst res-c-lst valid))))
     ((and* (cross-product-two-larges-enabled)
            (and-list-p single-pp)
            ;; when there's only one s, c, or s-c-res in single-pp:
            (cross-product-pp-pattern-check3 single-pp))
      (b* ((single-s/c1 (cadr (caddr single-pp)))
           (single-s/c2 (caddr (caddr single-pp)))
           ((mv s-lst pp-lst c-lst valid)
            (cross-product-two-larges-aux single-s/c1 single-s/c2))
           ((unless valid)
            (mv nil nil nil nil)))
        (mv (negate-lst s-lst negated)
            (negate-lst pp-lst negated)
            (negate-lst c-lst negated)
            t)))
     (t (mv nil nil nil nil)))))

;; (define cross-product-two-larges ((single-pp rp-termp))
;;   :returns (mv (res-s-lst  rp-term-listp :hyp (rp-termp single-pp))
;;                (res-pp-lst rp-term-listp :hyp (rp-termp single-pp))
;;                (res-c-lst  rp-term-listp :hyp (rp-termp single-pp))
;;                (valid booleanp))
;;   (b* (((mv single-pp negated) (case-match single-pp
;;                                  (('-- in) (mv in t))
;;                                  (& (mv single-pp nil)))))
;;     (cond
;;      ((and (cross-product-two-larges-enabled)
;;            (and-list-p single-pp)
;;            ;; when there's only one s, c, or s-c-res in single-pp:
;;            (cross-product-pp-pattern-check3 single-pp))
;;       (b* ((single-s/c1 (cadr (caddr single-pp)))
;;            (single-s/c2 (caddr (caddr single-pp)))
;;            ((mv s-lst pp-lst c-lst valid)
;;             (cross-product-two-larges-aux single-s/c1 single-s/c2)))
;;         (mv s-lst pp-lst c-lst valid)))
;;      (t

(define count-repetitions-at-head (lst)
  :returns (rep-count natp)
  (if (atom lst)
      0
    (if (atom (cdr lst))
        1
      (if (equal (car lst) (cadr lst))
          (1+ (count-repetitions-at-head (cdr lst)))
        1)))
  ///
  (defret posp-of-<fn>
    (implies (consp lst)
             (posp rep-count)))
  (defret rep-count-is-less-than-lst-len-for-<fn>
    (<= rep-count (len lst))))

(define repeat-s-sum-lst ((lst rp-term-listp)
                          (rep-count natp))
  :returns (res-lst rp-term-listp :hyp (rp-term-listp lst))
  :verify-guards :after-returns
  (if (zp rep-count)
      nil
    (s-sum-merge-aux lst (repeat-s-sum-lst lst (1- rep-count)))))

(define repeat-pp-sum-lst ((lst rp-term-listp)
                           (rep-count natp))
  :returns (res-lst rp-term-listp :hyp (rp-term-listp lst))
  :verify-guards :after-returns
  (if (zp rep-count)
      nil
    (pp-sum-merge-aux lst (repeat-pp-sum-lst lst (1- rep-count)))))

(local
 (defthm rp-term-listp-of-nthcdr
   (implies (and (rp-term-listp lst)
                 (<= num (len lst)))
            (rp-term-listp (nthcdr num lst)))
   :hints (("Goal"
            :in-theory (e/d (nthcdr len)
                            ())))))

(define cross-product-pp-aux2 ((pp-lst rp-term-listp))
  :returns (mv (res-s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  :measure (len pp-lst)
  :prepwork ((local
              (defthm len-of-nthcdr
                (implies (and (consp pp-lst)
                              (posp num)
                              (<= num (len pp-lst)))
                         (< (len (nthcdr num pp-lst))
                            (len pp-lst)))
                :hints (("goal"
                         :in-theory (e/d (len nthcdr) ()))))))
  :verify-guards :after-returns
  (if (atom pp-lst)
      (mv nil nil nil)
    (b* (((mv res-s-lst res-pp-lst res-c-lst valid)
          (cross-product-pp-aux (car pp-lst)))

         ;; see if partial products repeat, then try not to repeat work in the
         ;; next iterations of cross-product-pp-aux2
         (rep-count (count-repetitions-at-head pp-lst)) ;;
         (res-s-lst (repeat-s-sum-lst res-s-lst rep-count))
         (res-pp-lst (repeat-pp-sum-lst res-pp-lst rep-count))
         (res-c-lst (repeat-s-sum-lst res-c-lst rep-count))

         (next-args (nthcdr rep-count pp-lst))
         ((mv rest-s-lst rest-pp-lst rest-c-lst)
          (cross-product-pp-aux2 next-args))) ;;
      (if valid
          (mv (s-sum-merge-aux res-s-lst rest-s-lst)
              (pp-sum-merge-aux res-pp-lst rest-pp-lst)
              (s-sum-merge-aux res-c-lst rest-c-lst))
        (mv rest-s-lst
            (cond ((equal rep-count 1)
                   (cons-with-hint (car pp-lst)
                                   rest-pp-lst
                                   pp-lst))
                  ((equal rest-pp-lst next-args)
                   pp-lst)
                  (t
                   (append (repeat rep-count (car pp-lst))
                           rest-pp-lst)))
            rest-c-lst)))))

(define cross-product-pp ((pp-lst rp-term-listp))
  :returns (mv (res-s-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
               (res-c-lst rp-term-listp :hyp (rp-term-listp pp-lst)))
  "Applicable elements in pp-lst will be tried for cross product. For example,
  (and$ x (s a b c)) may become (s (and$ a x) (and$ b x) (and$ c x))"
  (b* (((mv res-s-lst res-pp-lst res-c-lst)
        (cross-product-pp-aux2 pp-lst))
       (res-pp-lst (if (pp-lst-orderedp res-pp-lst)
                       res-pp-lst
                     (pp-sum-sort-lst res-pp-lst))))
    (mv res-s-lst res-pp-lst res-c-lst)))

(define pp-lst-is-a-part-of-radix8+-summation ((pp-lst))
  :returns (res booleanp)
  (if (atom pp-lst)
      (equal pp-lst nil)
    (b* ((cur (ex-from-rp-loose (car pp-lst))))
      (and (or (equal cur ''1)
               (logbit-p cur)
               (and (binary-not-p cur)
                    (logbit-p (cadr cur))))
           (pp-lst-is-a-part-of-radix8+-summation (cdr pp-lst))))))

(define pp-is-a-part-of-radix8+-summation ((cur))
  :returns (res booleanp)
  (and (or (equal cur ''1)
           (logbit-p cur)
           (and (binary-and-p cur)
                (or (logbit-p (ex-from-rp-loose (cadr cur)))
                    (quotep (cadr cur)))
                (or (logbit-p (ex-from-rp-loose (caddr cur)))
                    (quotep (caddr cur))))
           (and (binary-not-p cur)
                (logbit-p (ex-from-rp-loose (cadr cur)))))))

;;;;;;;;

;;;;;;;;;;;;;;;;;;;

(define is-bitp-svl-bits ((term-orig rp-termp))
  (and (has-integerp-rp term-orig)
       (b* ((term (ex-from-rp$ term-orig)))
         (case-match term
           (('svl::bits & & ''1)
            t)))))

(define memoized-cons (x y)
  :enabled t
  (cons x y)

  )

(define extract-new-sum-element ((term rp-termp) acc)
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)
                              (rp-term-listp acc)))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((term-orig term)
       (term (ex-from-rp$ term))
       ((mv abs-term ?negated)
        (case-match term (('-- e) (mv (ex-from-rp$ e) t)) (& (mv term nil)))))
    (cond
     ((single-c-p abs-term)
      (memoized-cons term-orig acc))
     ((single-s-p abs-term)
      (memoized-cons term-orig acc))
     ((single-s-c-res-p abs-term)
      (memoized-cons term-orig acc))
     ((sum-list-p abs-term)
      (memoized-cons term-orig acc))
     ((and-list-p abs-term)
      (memoized-cons term-orig acc))
     ((binary-sum-p term)
      (b* ((acc (extract-new-sum-element (cadr term) acc))
           (acc (extract-new-sum-element (caddr term) acc)))
        acc))
     ((quote-p term)
      (b* ((x (ifix (cadr term)))) ;; ifix here is ok because sum-list calls sum which
        ;; calls ifix for its arguments..
        (cond ((natp x) (append (repeat x ''1) acc))
              (t (append (repeat (- x) '(-- '1)) acc)))))
     ((or (pp-term-p abs-term)
          (binary-fnc-p abs-term)
          (has-bitp-rp term-orig))
      (memoized-cons term-orig acc))
     ((is-bitp-svl-bits term-orig)
      (cons `(rp 'bitp ,term-orig) acc))
     (t
      (progn$
       (hard-error 'extract-new-sum-element
                   "Unexpexted term: ~p0 ~%"
                   (list (cons #\0 term-orig)))
       (memoized-cons term-orig acc))))))

(define extract-new-sum-consed ((term rp-termp))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :prepwork
  ((local
    (in-theory (enable ex-from-rp))))
  :returns (acc-res rp-term-listp
                    :hyp (and (rp-termp term)))
  (b* ((term-orig term)
       (term (ex-from-rp$ term)))
    (case-match term
      (('cons x rest)
       (b* ((acc (extract-new-sum-consed rest)))
         (extract-new-sum-element x acc)))
      (''nil
       nil)
      (('quote x)
       (if (consp x)
           (extract-new-sum-element (list 'quote (sum-list x)) nil)
         (progn$
          (hard-error 'extract-new-sum-consed
                      "Unexpected term. Should be a true-listp formm: ~p0~%"
                      (list (cons #\0 term-orig)))
          (list-to-lst term-orig)
          )))
      (&
       (progn$
        (hard-error 'extract-new-sum-consed
                    "Unexpected term. Should be a true-listp formm: ~p0~%"
                    (list (cons #\0 term-orig)))
        (list-to-lst term-orig)
;(list `(sum-list ,term-orig))
        ))
      )))

(define new-sum-merge-aux-dissect-term ((term rp-termp))
  :inline t
  :returns (mv (term-orig rp-termp :hyp (rp-termp term))
               (abs-term-w/-sc rp-termp :hyp (rp-termp term))
               (abs-term rp-termp :hyp (rp-termp term))
               (negated booleanp))
  (b* ((term-orig term)
       ((mv abs-term-w/-sc negated)
        (case-match term-orig (('-- e) (mv e t)) (& (mv term-orig nil))))
       (abs-term (ex-from-rp$ abs-term-w/-sc)))
    (mv term-orig abs-term-w/-sc abs-term negated)))

(define new-sum-merge-aux-add-negated-coughed ((to-be-coughed-c-lst rp-term-listp)
                                               (abs-term-w/-sc rp-termp)
                                               negated)
  :inline t
  :returns (res-lst rp-term-listp :hyp (and (rp-term-listp to-be-coughed-c-lst)
                                            (rp-termp abs-term-w/-sc)))
  (if negated
      (s-sum-merge-aux to-be-coughed-c-lst
                       (list `(-- ,abs-term-w/-sc)))
    to-be-coughed-c-lst))

;;(include-book "pp-flatten-wrapper")

(defsection extract-equals-from-pp-lst

  (define extract-equals-from-pp-lst-precheck (e-lst)
    (if (atom e-lst)
        nil
      (or (is-equals (ex-from-rp-loose (car e-lst)))
          (extract-equals-from-pp-lst-precheck (cdr e-lst)))))

  (define extract-equals-from-pp-lst-aux ((e-lst rp-term-listp))
    :returns (mv (res-e-lst rp-term-listp :hyp (rp-term-listp e-lst))
                 (res-pp-lst rp-term-listp :hyp (rp-term-listp e-lst)))
    (if (atom e-lst)
        (mv nil nil)
      (b* ((cur (ex-from-rp$ (car e-lst)))
           ((when (and (is-equals cur)
                       (pp-term-p (caddr cur))))
            (mv (cdr e-lst)
                (pp-flatten (caddr cur) nil)))
           ((mv rest1 rest2)
            (extract-equals-from-pp-lst-aux (cdr e-lst))))
        (mv (cons-with-hint (car e-lst) rest1 e-lst)
            rest2))))

  (define extract-equals-from-pp-lst ((pp-lst rp-term-listp)
                                      (limit natp))
    :measure (acl2::nat-list-measure (list limit (len pp-lst)))
    :returns (res-lst rp-term-listp :hyp (rp-term-listp pp-lst))
    :verify-guards :after-returns
    (b* (((when (zp limit)) pp-lst)
         ((when (atom pp-lst)) nil)
         ;; skip repeateds because they'll either be coughed or removed.
         ((when (and (consp (cdr pp-lst))
                     (rp-equal-cnt (first pp-lst)
                                   (second pp-lst)
                                   1)))
          (cons-with-hint (first pp-lst)
                          (cons-with-hint (second pp-lst)
                                          (extract-equals-from-pp-lst (cddr pp-lst) limit)
                                          (cdr pp-lst))
                          pp-lst))
            
         (rest (extract-equals-from-pp-lst (cdr pp-lst) limit))
         (cur (car pp-lst))
         ((mv cur signed)
          (case-match cur (('-- x) (mv x t))
            (& (mv cur nil))))
         (cur (ex-from-rp$ cur))
         ((when (is-equals cur))
          (cons (if signed `(-- ,(cadr cur)) (cadr cur)) rest))
         
         ((mv e-lst valid)
          (case-match cur (('and-list & ('list . lst)) (mv lst t))
            (& (mv nil nil))))
         ((unless (and valid
                       (extract-equals-from-pp-lst-precheck e-lst)))
          (cons-with-hint (car pp-lst) rest pp-lst))

         ((mv res-e-lst res-pp-lst)
          (extract-equals-from-pp-lst-aux e-lst))

         ((unless res-pp-lst)
          (cons-with-hint (car pp-lst) rest pp-lst))
          
         ((mv res-pp-lst2 valid)
          (cross-product-pp-aux-for-pp-lst res-pp-lst res-e-lst))
         ((unless valid)
          (cons-with-hint (car pp-lst) rest pp-lst))
         (res-pp-lst3 (extract-equals-from-pp-lst (negate-lst res-pp-lst2 signed)
                                                  (1- limit))))
      (pp-sum-merge-aux res-pp-lst3
                        rest)))

  ;; just for debugging...
  (define check-if-clearable-equals-in-pp-lst (pp-lst)
    (b* (((when (atom pp-lst)) nil)
         ((when (and (consp (cdr pp-lst))
                     (rp-equal-cnt (first pp-lst)
                                   (second pp-lst)
                                   1)))
          (check-if-clearable-equals-in-pp-lst (cddr pp-lst)))
         (cur (ex-from-rp-loose (car pp-lst)))
         (cur (case-match cur (('-- x) x) (& cur)))
         ((when (is-equals cur)) t)
         ((mv e-lst valid)
          (case-match cur (('and-list & ('list . lst)) (mv lst t))
            (& (mv nil nil)))))
      (or (and valid
               (extract-equals-from-pp-lst-precheck e-lst))
           (check-if-clearable-equals-in-pp-lst (cdr pp-lst))))))
         

(defconst *large-number*
  (expt 2 32))

(define new-sum-merge-aux ((sum-lst rp-term-listp)
                           (limit natp))
  :verify-guards nil
  :measure (acl2::nat-list-measure (list limit (len sum-lst)))
  :returns (mv (s) (pp-lst) (c-lst) (to-be-coughed-c-lst))
  (b* (((when (zp limit)) (mv ''nil sum-lst nil (raise "Limit ~
  reached. This is highly unexpected. Something must have gone wrong.")))
       ((when (atom sum-lst))
        (mv ''nil nil nil nil))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux (cdr sum-lst) limit))
       ((mv term-orig abs-term-w/-sc abs-term negated)
        (new-sum-merge-aux-dissect-term (car sum-lst))))
    (cond
     ((single-c-p abs-term)
      (b* (((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst2)
            (c-sum-merge-main (list abs-term-w/-sc) c-lst
                              :auto-swap nil
                              :clean-c1-lst nil
                              :cough-c-lst t))
           (s (s-sum-merge s coughed-s))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst2))
           (to-be-coughed-c-lst
            (new-sum-merge-aux-add-negated-coughed to-be-coughed-c-lst
                                                   abs-term-w/-sc
                                                   negated))
           (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((single-s-p abs-term)
      (b* ((s (s-sum-merge s (create-list-instance
                              (list term-orig)))))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((single-s-c-res-p abs-term)
      (b* (((mv s-arg pp-arg c-arg)
            (case-match abs-term
              (('s-c-res s-arg pp-arg c-arg) (mv s-arg pp-arg c-arg))
              (& (mv ''nil ''nil ''nil))))
           ((mv s-arg pp-arg c-arg-lst)
            (mv (negate-list-instance s-arg negated)
                (negate-list-instance pp-arg negated)
                (negate-lst (list-to-lst c-arg) negated)))
           ((mv to-be-coughed-c-lst2 c-arg-lst)
            (cough-lst c-arg-lst))

           ((mv coughed-s coughed-pp-lst c-lst to-be-coughed-c-lst3)
            (c-sum-merge-main c-arg-lst c-lst
                              :auto-swap nil
                              :clean-c1-lst t
                              :cough-c-lst t))

           (s (s-sum-merge s s-arg))
           (s (s-sum-merge s coughed-s))
           (pp-lst (pp-sum-merge-aux (list-to-lst pp-arg) pp-lst))
           (pp-lst (pp-sum-merge-aux coughed-pp-lst pp-lst))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst2))
           (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst
                                                 to-be-coughed-c-lst3))
           )
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((sum-list-p abs-term)
      (b* ((arg-pp (cadr abs-term))
           (arg-pp (negate-list-instance arg-pp negated))
           (pp-lst (pp-sum-merge-aux (list-to-lst arg-pp)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((and-list-p abs-term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((quote-p abs-term)
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((is-equals abs-term)
      (b* (((mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2)
            (new-sum-merge-aux (list (cadr abs-term)) (1- limit)))
           ((mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2)
            (mv (negate-list-instance s2 negated)
                (negate-lst pp-lst2 negated)
                (negate-lst c-lst2 negated)
                (negate-lst to-be-coughed-c-lst2 negated))))
        (mv (s-sum-merge s s2)
            (pp-sum-merge-aux pp-lst pp-lst2)
            (s-sum-merge-aux c-lst c-lst2)
            (s-sum-merge-aux to-be-coughed-c-lst to-be-coughed-c-lst2))))
     ((pp-term-p abs-term-w/-sc)
      (b* (;;(abs-term (4vec->pp-term abs-term))
           (pp-lst2 (pp-flatten-with-binds
                     abs-term-w/-sc negated
                     :disabled (and (unpack-booth-later-enabled)
                                    (not
                                     (pp-is-a-part-of-radix8+-summation abs-term-w/-sc)))))

           (?orig-pp-lst2 pp-lst2)
           ;;(pp-lst2 (extract-equals-from-pp-lst pp-lst2 *large-number*))

           #|(- (or (check-if-clearable-equals-in-pp-lst pp-lst2)
                  (raise "?orig-pp-lst2: ~p0, pp-lst2: ~p1 ~%" orig-pp-lst2 pp-lst2)))|#
           
           ((mv s-lst2 pp-lst2 c-lst2) (ex-from-pp-lst pp-lst2))
           (s (s-sum-merge s (create-list-instance s-lst2)))
           (c-lst (s-sum-merge-aux c-lst c-lst2))

           ((mv s-lst2 pp-lst2 c-lst2) (cross-product-pp pp-lst2))
           (s (s-sum-merge s (create-list-instance s-lst2)))
           (c-lst (s-sum-merge-aux c-lst c-lst2))

           ((mv pp-lst2 recollected-c-lst) (recollect-pp-lst-to-sc-main pp-lst2))
           (c-lst (s-sum-merge-aux recollected-c-lst c-lst))
           (pp-lst (pp-sum-merge-aux pp-lst pp-lst2)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     ((binary-fnc-p abs-term) ;; this can still be reached if some inner term
      ;; is not pp-term-p.
      (b* ((pp-lst (pp-sum-merge-aux (list term-orig)  pp-lst)))
        (mv s pp-lst c-lst to-be-coughed-c-lst)))
     (t
      (progn$ (hard-error 'new-sum-merge-aux
                          "Unexpected term ~p0 ~%"
                          (list (cons #\0 abs-term-w/-sc)))
              (mv `(cons ,term-orig ,s)
                  pp-lst
                  c-lst
                  to-be-coughed-c-lst)))))
  ///
  (acl2::defret
    return-vals--of--<fn>
    :hyp (rp-term-listp sum-lst)
    (and (rp-termp s)
         (rp-term-listp pp-lst)
         (rp-term-listp c-lst)
         (rp-term-listp to-be-coughed-c-lst))
    :hints (("Goal"
             :do-not-induct t
             :expand ((new-sum-merge-aux sum-lst limit))
             :induct (new-sum-merge-aux sum-lst limit)
             :in-theory (e/d ((:induction new-sum-merge-aux))
                             ((:definition new-sum-merge-aux)
                              (:e tau-system)
                              (:rewrite default-car)
                              (:rewrite default-cdr)
                              (:rewrite rp-termp-implies-subterms))))))
  (verify-guards new-sum-merge-aux))

(define extract-from-equals-lst ((pp-lst rp-term-listp))
  :returns (mv (s) (res-pp-lst) (c-lst) (to-be-coughed-c-lst) changed)
  :verify-guards nil
  (if (atom pp-lst)
      (mv ''0 nil nil nil nil)
    (b* ((cur-orig (car pp-lst))
         (rest (cdr pp-lst))
         ((mv s1 pp-lst1 c-lst1 to-be-coughed-c-lst1 changed1)
          (extract-from-equals-lst rest))
         ((mv cur negated)
          (case-match cur-orig
            (('-- cur) (mv (ex-from-rp$ cur) t))
            (& (mv (ex-from-rp$ cur-orig) nil))))
         
         ((mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2 changed2)
          (case-match cur
            (('equals & &)
             (b* (((mv s pp-lst c-lst to-be-coughed-c-lst)
                   (new-sum-merge-aux (list (cadr cur)) *large-number*)))
               (mv s pp-lst c-lst to-be-coughed-c-lst t)))
            (&
             (if (and (consp cur)
                      (or (equal (first cur) 's)
                          (equal (first cur) 'c)
                          (equal (first cur) 's-c-res)))
                 (b* (((mv s pp-lst c-lst to-be-coughed-c-lst)
                       (new-sum-merge-aux (list cur) *large-number*)))
                   (mv s pp-lst c-lst to-be-coughed-c-lst t))
               (mv cur nil nil nil nil)))))
         ((mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2)
          (if changed2
              (mv (negate-list-instance s2 negated)
                  (negate-lst pp-lst2 negated)
                  (negate-lst c-lst2 negated)
                  (negate-lst to-be-coughed-c-lst2 negated))
            (mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2))))
      (cond ((and changed1 changed2)
             (mv (s-sum-merge s1 s2)
                 (pp-sum-merge-aux pp-lst1 pp-lst2)
                 (s-sum-merge-aux c-lst1 c-lst2)
                 (s-sum-merge-aux to-be-coughed-c-lst1 to-be-coughed-c-lst2)
                 t))
            (changed1
             (mv s1
                 (cons cur-orig pp-lst1)
                 c-lst1
                 to-be-coughed-c-lst1
                 t))
            (changed2
             (mv s2
                 (pp-sum-merge-aux rest pp-lst2)
                 c-lst2
                 to-be-coughed-c-lst2
                 t))
            (t (mv ''nil nil nil nil nil)))))
  ///
  (acl2::defret
    return-vals--of--<fn>
    :hyp (rp-term-listp pp-lst)
    (and (rp-termp s)
         (rp-term-listp res-pp-lst)
         (rp-term-listp c-lst)
         (rp-term-listp to-be-coughed-c-lst)))

  (verify-guards extract-from-equals-lst
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ())))))

(progn
  (encapsulate
    (((undo-rw-and-open-up-adders-enabled) => *))
    (local
     (defun undo-rw-and-open-up-adders-enabled ()
       nil)))

  (defmacro enable-undo-rw-and-open-up-adders (enable)
    (if enable
        `(defattach undo-rw-and-open-up-adders-enabled return-t)
      `(defattach undo-rw-and-open-up-adders-enabled return-nil)))

  (enable-undo-rw-and-open-up-adders t))

(define new-sum-merge ((term rp-termp))
  :verify-guards t
  :returns (mv (s) (pp-lst) (c-lst) (to-be-coughed-c-lst))
  (b* ((sum-lst (extract-new-sum-consed term))
       ((mv s pp-lst c-lst to-be-coughed-c-lst)
        (new-sum-merge-aux sum-lst *large-number*))

       (pp-lst (if (check-if-clearable-equals-in-pp-lst pp-lst)
                   (b* ((- (cw "Undo-able adder is found. "))
                        ((unless (undo-rw-and-open-up-adders-enabled))
                         (progn$ (cw " However, undoing adder rw feature is disabled. See :doc ~p0 for details.~%"
                                     'Multiplier-Verification-Heuristics)
                                 pp-lst))
                        (- (cw "Now, undoing rw and opening up some adders. See :doc ~p0 if too slow. ~%"
                               'Multiplier-Verification-Heuristics))
                        (pp-lst (extract-equals-from-pp-lst pp-lst *large-number*))
                        (- (cw "Undoing rw (extract-equals-from-pp-lst) finished. ~%"))
                        #|(- (and (check-if-clearable-equals-in-pp-lst pp-lst)
                             (raise "pp-lst : ~p0 ~%" pp-lst)))|#
                        )
                     pp-lst)
                 pp-lst))
       
       ((mv s2 pp-lst2 c-lst2 to-be-coughed-c-lst2 changed2)
        (extract-from-equals-lst pp-lst))

       
       
       ((unless changed2) ;; should not be logically necessary but mabe will
        ;; have some runtime performance benfits 
        (mv s pp-lst c-lst to-be-coughed-c-lst))
       )
    (mv (s-sum-merge s s2)
        (if (pp-lst-orderedp pp-lst2) pp-lst2 (pp-sum-sort-lst pp-lst2))
        (s-sum-merge-aux c-lst c-lst2)
        (s-sum-merge-aux to-be-coughed-c-lst to-be-coughed-c-lst2)))
  ///
  (acl2::defret
    return-vals--of--<fn>
    :hyp (rp-termp term)
    (and (rp-termp s)
         (rp-term-listp pp-lst)
         (rp-term-listp c-lst)
         (rp-term-listp to-be-coughed-c-lst))))

;; (progn
#|(define well-formed-new-sum ((term rp-termp))
:returns (res booleanp)
(or nil
(case-match term
(('cons x rest)
(b* ((x (ex-from-rp$ x))
(rest-res (well-formed-new-sum rest)))
(cond ((good-4vec-term-p x)
rest-res)
((case-match x (('and-list & &) t))
rest-res)
((case-match x (('s & & &) t))
rest-res)
((case-match x (('c & & & &) t))
rest-res)
#|((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
rest-res)||#
((case-match x (('s-c-res & & &) t))
rest-res)
((case-match x (('sum-list &) t))
rest-res)
((equal x ''0)
rest-res)
(t
nil))))
(('quote x)
(integer-listp x))
(& nil))))||#

(progn
  (define light-pp-term-p ((term rp-termp))
    :inline t
    (or
     (has-bitp-rp term)
     (b* ((term (ex-from-rp$ term)))
       (case-match term
         (('binary-not &)
          t)
         (('binary-and & &)
          t)
         (('binary-or & &)
          t)
         (('binary-xor & &)
          t)
         (('binary-? & & &)
          t)
         (('logbit$inline & &)
          t)
         (''1
          t)))))

  (define light-pp-term-list-p ((lst rp-term-listp))
    (if (atom lst)
        (equal lst nil)
      (and (light-pp-term-p (car lst))
           (light-pp-term-list-p (cdr lst)))))

  (define quarternaryp-sum-aux ((term rp-termp))
    :returns (mv (res natp
                      :rule-classes (:rewrite :type-prescription))
                 (valid booleanp))
    :verify-guards nil
    :prepwork ((local
                (in-theory (disable natp)))
               (local
                (defthm lemma1
                  (implies (NAT-LISTP lst)
                           (natp (sum-list lst)))
                  :hints (("Goal"
                           :induct (sum-list lst)
                           :do-not-induct t
                           :in-theory (e/d (sum-list
                                            nat-listp
                                            sum)
                                           (+-is-sum))))
                  :rule-classes (:type-prescription :rewrite))))
    (case-match term
      (('cons x rest)
       (b* (((mv rest-sum valid) (quarternaryp-sum-aux rest))
            ((unless valid)
             (mv 0 nil))
            (x-orig x)
            (x (ex-from-rp$ x)))
         (cond ((light-pp-term-p x)
                (mv (1+ rest-sum) t))
               ((single-s-p x)
                (mv (1+ rest-sum) t))
               ((has-bitp-rp x-orig)
                (mv (1+ rest-sum) t))
               ((and-list-p x)
                (mv (1+ rest-sum) t))
               ((equal x ''0)
                (mv rest-sum t))
               ((equal x ''1)
                (mv (1+ rest-sum) t))
               #|((case-match x (('sum-list ''nil) t))
               (mv rest-sum t))||#
               ((sum-list-p x)
                (if (light-pp-term-list-p (list-to-lst (cadr x)))
                    (mv (+ rest-sum (len (list-to-lst (cadr x)))) t)
                  (mv 0 nil)))
               (t
                (mv 0 nil)))))
      (''nil
       (mv 0 t))
      (('quote x)
       (b* ((res (sum-list x)))
         (if (natp res)
             (mv res t)
           (mv 0 nil))))
      (& (mv 0 nil)))
    ///
    (verify-guards quarternaryp-sum-aux
      :hints (("Goal"
               :in-theory (e/d () ())))))

  (define quarternaryp-sum ((term rp-termp))
    :returns (mv (quarternaryp? booleanp)
                 (bitp? booleanp))
    (b* (((mv res valid)
          (quarternaryp-sum-aux term)))
      (mv (or (and valid
                   (quarternaryp res))
              #|(hard-error 'quarternarp-sum "term ~p0 ~%"
              (list (cons #\0 term)))||#)
          (and valid
               (bitp res))))))

#|(acl2::Defines
search-for-1
:hints (("Goal"
:in-theory (e/d (measure-lemmas) ())))
(define search-for-1 (term)
:measure (cons-count term)
(b* ((term (ex-from-rp term)))
(case-match term
(('s & pp c)
(or (and (consp (list-to-lst pp))
(equal (car (list-to-lst pp)) ''1))
(search-for-1-lst (list-to-lst c))))
(('s-c-res s & c)
(or (search-for-1-lst (list-to-lst s))
(search-for-1-lst (list-to-lst c))))
(('c & s pp c)
(or (and (consp (list-to-lst pp))
(equal (car (list-to-lst pp)) ''1))
(search-for-1-lst (list-to-lst s))
(search-for-1-lst (list-to-lst c))))
(& nil))))
(define search-for-1-lst (lst)
:measure (cons-count lst)
(if (atom lst)
nil
(or (search-for-1 (car lst))
(search-for-1-lst (cdr lst))))))||#

#|(rp::and-list-to-binary-and '(RP::AND-LIST '327716
(LIST (RP::LOGBIT OP1_LO '15)
(RP::LOGBIT OP2_LO '31))))||#

(define create-s-c-res-instance ((s-lst rp-term-listp)
                                 (pp-lst rp-term-listp)
                                 (c-lst rp-term-listp)
                                 (bitp booleanp))
  :inline t
  :returns (res rp-termp :hyp (and (rp-term-listp s-lst)
                                   (rp-term-listp pp-lst)
                                   (rp-term-listp c-lst)))
  :guard-hints (("Goal"
                 :in-theory (e/d (rp-term-listp) ())))
  (cond ((and (not pp-lst) (not c-lst)
              (consp s-lst) (not (cdr s-lst))
              (single-s-p (ex-from-rp$ (car s-lst))))
         (cond ((and bitp
                     (not (hide (is-rp (car s-lst)))))
                `(rp 'bitp ,(car s-lst)))
               (t (car s-lst))))
        ((and (not pp-lst) (not s-lst)
              (consp c-lst) (not (cdr c-lst))
              (single-c-p (ex-from-rp$ (car c-lst))))
         (cond ((and bitp
                     (not (hide (is-rp (car c-lst)))))
                `(rp 'bitp ,(car c-lst)))
               (t (car c-lst))))
        ((and (quoted-listp s-lst)
              (quoted-listp pp-lst)
              (quoted-listp c-lst))
         `',(s-c-res (unquote-all s-lst)
                     (unquote-all pp-lst)
                     (unquote-all c-lst)))
        (t
         (b* (((mv term valid) ;; if there is only one and-list, return its
               ;; binary-and equivalent instead.
               (if (and (not c-lst)
                        (not s-lst)
                        (consp pp-lst)
                        (not (cdr pp-lst)))
                   (and-list-to-binary-and (car pp-lst))
                 (mv nil nil)))
              ((when valid) term)

              (term `(s-c-res ,(create-list-instance s-lst)
                              ,(create-list-instance pp-lst)
                              ,(create-list-instance c-lst))))
           (if bitp
               `(rp 'bitp ,term)
             term)))))

(define s-spec-meta-aux ((s rp-termp)
                         (pp-lst rp-term-listp)
                         (c-lst rp-term-listp))
  :verify-guards t
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  (b* (((mv pp-lst c-lst) (s-of-s-fix-lst (list-to-lst s)
                                          pp-lst
                                          c-lst
                                          :clean-args (clean-pp-args-cond nil c-lst)))
       #| (pp-lst-before-clean pp-lst)||#
       (c-lst (s-fix-pp-args-aux c-lst))

       (pp-lst (if (clean-pp-args-cond nil c-lst)
                   (s-fix-pp-args-aux pp-lst)
                 pp-lst))
       (pp (create-list-instance pp-lst))
       (c (create-list-instance c-lst))

       ((mv res-s-lst res-pp-lst res-c-lst) (create-s-instance pp c)))
    (create-s-c-res-instance res-s-lst res-pp-lst res-c-lst t)))

(define c-spec-meta-aux ((arg-s rp-termp)
                         (arg-pp-lst rp-term-listp)
                         (arg-c-lst rp-term-listp)
                         (to-be-coughed-c-lst rp-term-listp)
                         (quarternaryp booleanp))
  :returns (res rp-termp
                :hyp (and (rp-termp arg-s)
                          (rp-term-listp arg-pp-lst)
                          (rp-term-listp to-be-coughed-c-lst)
                          (rp-term-listp arg-c-lst)))
  :verify-guards t
  :prepwork ((local
              (in-theory (disable natp))))
  (b* ((arg-s-lst (list-to-lst arg-s))

       ((mv arg-pp-lst arg-c-lst coughed-s-lst2 coughed-pp-lst2 to-be-coughed-c-lst)
        (if (c-of-s-fix-mode)
            (c-of-s-fix-lst arg-s-lst arg-pp-lst arg-c-lst to-be-coughed-c-lst)
          (mv arg-pp-lst arg-c-lst nil nil to-be-coughed-c-lst)))

       ((mv coughed-c-lst-from-args arg-c-lst)
        (c-fix-arg-aux arg-c-lst t))
       (to-be-coughed-c-lst (s-sum-merge-aux to-be-coughed-c-lst coughed-c-lst-from-args))

       ((mv coughed-s-lst arg-s-lst)
        (if (c-of-s-fix-mode)
            (mv nil nil)
          (c-fix-arg-aux arg-s-lst t)))

       ((mv coughed-pp-lst arg-pp-lst)
        (c-fix-arg-aux-with-cond arg-pp-lst t (clean-pp-args-cond arg-s-lst arg-c-lst)))

       ((mv arg-s-lst arg-pp-lst arg-c-lst
            coughed-s-lst coughed-pp-lst to-be-coughed-c-lst)
        (c-pattern3-reduce  arg-s-lst arg-pp-lst arg-c-lst
                            coughed-s-lst coughed-pp-lst to-be-coughed-c-lst))

       ((mv merged-s-lst merged-pp-lst merged-c-lst)
        (create-c-instance arg-s-lst arg-pp-lst arg-c-lst))

       (coughed-s-lst (s-sum-merge-aux coughed-s-lst merged-s-lst))
       (coughed-s-lst (s-sum-merge-aux coughed-s-lst coughed-s-lst2))
       (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst merged-pp-lst))
       (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst2 coughed-pp-lst))

       ((when (not to-be-coughed-c-lst))
        (create-s-c-res-instance coughed-s-lst coughed-pp-lst
                                 merged-c-lst quarternaryp))

       ((mv s-coughed2 coughed-pp-lst2 merged-c-lst &)
        (c-sum-merge-main to-be-coughed-c-lst merged-c-lst
                          :auto-swap nil
                          :clean-c1-lst t
                          :cough-c-lst nil))

       (coughed-s-lst (s-sum-merge-aux coughed-s-lst (list-to-lst s-coughed2)))

       (coughed-pp-lst (pp-sum-merge-aux coughed-pp-lst coughed-pp-lst2))

       (res (create-s-c-res-instance coughed-s-lst coughed-pp-lst merged-c-lst
                                     quarternaryp)))
    res))

(verify-guards cons-count)

(define s-c-spec-meta ((term rp-termp))
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  :prepwork ((local
              (defthm lemma1
                (IS-RP (LIST 'RP ''BITP x))
                :hints (("Goal"
                         :in-theory (e/d (is-rp) ()))))))
  :verify-guards t
  (b* ((result
        (case-match term
          (('s-c-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                 (new-sum-merge sum))

                ((mv quarternaryp ?bitp) (quarternaryp-sum sum))

                (s-res (if bitp
                           (create-s-c-res-instance (list-to-lst s)
                                                    pp-lst
                                                    (s-sum-merge-aux
                                                     to-be-coughed-c-lst
                                                     (s-sum-merge-aux
                                                      to-be-coughed-c-lst
                                                      c-lst))
                                                    t)
                         (s-spec-meta-aux s pp-lst c-lst)))
                (c-res (if bitp ''0
                         (c-spec-meta-aux s pp-lst c-lst
                                          to-be-coughed-c-lst quarternaryp)))
                ;;(- (if (< (cons-count s-res) 40) (cw "s-res is ~p0 and c-res is  ~p1 and input ~p2 ~%~%~%" s-res c-res term) nil))
                (res `(cons ,s-res (cons ,c-res 'nil))))
             res))
          (('c-s-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                 (new-sum-merge sum))
                ((mv quarternaryp ?bitp) (quarternaryp-sum sum))
                (s-res (if bitp (create-s-c-res-instance (list-to-lst s)
                                                         pp-lst
                                                         (s-sum-merge-aux
                                                          to-be-coughed-c-lst
                                                          (s-sum-merge-aux
                                                           to-be-coughed-c-lst
                                                           c-lst))
                                                         t)
                         (s-spec-meta-aux s pp-lst c-lst)))
                (c-res (if bitp
                           ''0
                         (c-spec-meta-aux s pp-lst c-lst
                                          to-be-coughed-c-lst quarternaryp))))
             `(cons ,c-res (cons ,s-res 'nil))))
          (('s-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst);;(mv s pp c)
                 (new-sum-merge sum))
                ((mv ?quarternaryp ?bitp) (quarternaryp-sum sum)))
             (if bitp
                 (create-s-c-res-instance (list-to-lst s)
                                          pp-lst
                                          (s-sum-merge-aux
                                           to-be-coughed-c-lst
                                           (s-sum-merge-aux
                                            to-be-coughed-c-lst
                                            c-lst))
                                          t)
               (s-spec-meta-aux s pp-lst c-lst))))
          (('c-spec sum)
           (b* (((mv s pp-lst c-lst to-be-coughed-c-lst)
                 (new-sum-merge sum))
                ((mv quarternaryp ?bitp) (quarternaryp-sum sum)))
             (if bitp
                 ''0
               (c-spec-meta-aux s pp-lst c-lst to-be-coughed-c-lst quarternaryp))))
          (& term)))

       )
    (mv result t)))

#|

(s-spec-meta `(s-spec (cons (binary-and (logbit a 0) (logbit b 0))
(cons (binary-or (binary-and (logbit a 0) (logbit b 0))
(binary-and (logbit a 0) (logbit b 0)))
(cons (binary-and (logbit a 0) (logbit b 0))
(cons (binary-and (logbit a 1) (logbit
b 0))
'nil
))))))
||#
;;;;;;;;;;;;;;;;;;;;
