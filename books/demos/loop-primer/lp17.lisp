; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; (certify-book "lp17")
; (ld "lp17.lisp" :ld-pre-eval-print t)

(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; -----------------------------------------------------------------
; LP17-1

; Write a do loop$ that reverses the list lst.  For example, if lst is (A B C)
; the result should be (C B A).  Prove that your do loop$ is equal to (rev
; lst), where

(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x)) (list (car x)))))

(defun rev1 (x ac)
  (if (endp x)
      ac
      (rev1 (cdr x) (cons (car x) ac))))

(defthm lp17-1-lemma1
  (equal (loop$ with x = lst
                with ans = ans0
                do
                (if (consp x)
                    (progn (setq ans (cons (car x) ans))
                           (setq x (cdr x)))
                    (return ans)))
         (rev1 lst ans0)))

(defthm lp17-1-lemma2
  (equal (rev1 lst ans0)
         (append (rev lst) ans0)))

; Note that we could have stated our main theorem with endp instead of consp
; and the required lemma1 would be unchanged.

(defthm lp17-1-main
  (equal (loop$ with x = lst
                with ans = nil
                do
                (if (consp x)
                    (progn (setq ans (cons (car x) ans))
                           (setq x (cdr x)))
                    (return ans)))
         (rev lst)))

; -----------------------------------------------------------------
; LP17-2

; Write a do loop$ that computes (member e lst) and prove it correct.

(defthm lp17-2
  (equal (loop$ with x = lst
                do
                (if (consp x)
                    (if (equal (car x) e)
                        (return x)
                        (setq x (cdr x)))
                    (return nil)))
         (member e lst)))

; -----------------------------------------------------------------
; LP17-3

; Prove the following:

; (defthm lp17-3-main
;   (equal (loop$ with x = lst
;                 with ans = 0
;                 do
;                 (cond ((endp x) (return ans))
;                       (t (progn (setq ans (+ 1 ans))
;                                 (setq x (cdr x))))))
;          (len lst)))

(defun len-ac (x ans)
  (if (consp x)
      (len-ac (cdr x) (+ 1 ans))
      ans))

(defthm lp17-3-lemma1
  (equal (loop$ with x = lst
                with ans = ans0
                do
                (if (consp x)
                    (progn (setq ans (+ 1 ans))
                           (setq x (cdr x)))
                    (return ans)))
         (len-ac lst ans0)))

(defthm lp17-3-lemma2
  (implies (acl2-numberp ans0)
           (equal (len-ac lst ans0)
                  (+ ans0 (len lst)))))

(defthm lp17-3-main
  (equal (loop$ with x = lst
                with ans = 0
                do
                (cond ((endp x) (return ans))
                      (t (progn (setq ans (+ 1 ans))
                                (setq x (cdr x))))))
         (len lst)))


;-----------------------------------------------------------------
; lp17-4

; Write a do loop$ that computes (nth n lst), when n is a natural number.
; Prove it correct.

(defthm lp17-4
  (implies (natp n)
           (equal (loop$ with x = lst
                         with i = n
                         do
                         (cond ((endp x) (return nil))
                               ((equal i 0) (return (car x)))
                               (t (progn (setq i (- i 1))
                                         (setq x (cdr x))))))
                  (nth n lst))))

; -----------------------------------------------------------------
; lp17-5

; Prove the following:

; (defthm lp17-5-main
;   (implies (true-listp lst)
;            (equal (loop$ with x = lst
;                          with ans = nil
;                          do
;                          (cond ((endp x) (return ans))
;                                (t (progn (setq ans (append ans (list (car x))))
;                                          (setq x (cdr x))))))
;                   lst)))

(defun copy-ac (x ans)
  (if (consp x)
      (copy-ac (cdr x) (append ans (list (car x))))
      ans))

(defthm lp17-5-lemma1
  (equal (loop$ with x = lst
                with ans = ans0
                do
                (if (consp x)
                    (progn (setq ans (append ans (list (car x))))
                           (setq x (cdr x)))
                    (return ans)))
         (copy-ac lst ans0)))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm lp17-5-lemma2
  (implies (and (true-listp lst)
                (true-listp ans0))
           (equal (copy-ac lst ans0)
                  (append ans0 lst)))
  :hints (("Goal" :induct (copy-ac lst ans0))))

(defthm lp17-5-main
  (implies (true-listp lst)
           (equal (loop$ with x = lst
                         with ans = nil
                         do
                         (cond
                          ((endp x) (return ans))
                          (t (progn (setq ans (append ans (list (car x))))
                                    (setq x (cdr x))))))
                  lst)))

; -----------------------------------------------------------------
; lp17-6

; Prove the following.

; (defthm lp17-6-main
;   (implies (and (natp m)
;                 (natp n))
;            (equal (loop$ with i = m
;                          with j = n
;                          do
;                          (if (zp i)
;                              (return j)
;                              (progn (setq i (- i 1))
;                                     (setq j (+ j 1)))))
;                   (+ m n))))

(defun plus-ac (i j)
  (if (zp i)
      j
      (plus-ac (- i 1) (+ j 1))))

(defthm lp17-6-lemma1
  (implies (and (natp m)
                (natp n))
           (equal (loop$ with i = m
                         with j = n
                         do
                         (if (integerp i)
                             (if (< 0 i)
                                 (progn (setq i (- i 1))
                                        (setq j (+ 1 j)))
                                 (return j))
                             (return j)))
                  (plus-ac m n))))

(defthm lp17-6-lemma2
  (implies (and (natp m)
                (natp n))
           (equal (plus-ac m n)
                  (+ m n))))

(defthm lp17-6-main
  (implies (and (natp m)
                (natp n))
           (equal (loop$ with i = m
                         with j = n
                         do
                         (if (zp i)
                             (return j)
                             (progn (setq i (- i 1))
                                    (setq j (+ j 1)))))
                  (+ m n))))

; -----------------------------------------------------------------
; lp17-7

; Write a do loop$ that computes (fact n), for natural number n, where

(defun fact (n)
  (if (zp n)
      1
      (* n (fact (- n 1)))))

; and prove it correct.

(defun fact-ac (n ans)
  (if (zp n)
      ans
      (fact-ac (- n 1) (* ans n))))

(defthm lp17-7-lemma1
  (implies (natp n)
           (equal (loop$ with i = n
                         with ans = ans0
                         do
                         (if (integerp i)
                             (if (< 0 i)
                                 (progn (setq ans (* i ans))
                                        (setq i (- i 1)))
                                 (return ans))
                             (return ans)))
                  (fact-ac n ans0))))

(defthm lp17-7-lemma2
  (implies (and (natp n)
                (natp ac0))
           (equal (fact-ac n ac0)
                  (* (fact n) ac0))))

(defthm lp17-7-main
  (implies (natp n)
           (equal (loop$ with i = n
                         with ans = 1
                         do
                         (if (zp i)
                             (return ans)
                             (progn (setq ans (* i ans))
                                    (setq i (- i 1)))))
                  (fact n))))

; -----------------------------------------------------------------
; LP17-8

; Scan a list of numbers once and return the sum of the elements and the sum of
; the squares (with sq) of the elements as a cons pair.  E.g., given (1 2 3 4
; 5) return (cons (+ 1 2 3 4 5) (+ (sq 1) (sq 2) (sq 3) (sq 4) (sq 5))) = (15
; . 55).

; Prove that your do loop$ is equal to

; (cons (loop$ for e in lst sum e)
;       (loop$ for e in lst sum (sq e)))

(defun sq (x) (* x x))
(defwarrant sq)

(defun sum-and-sum-sq (lst u v)
  (cond
   ((endp lst) (cons u v))
   (t (sum-and-sum-sq (cdr lst)
                      (+ (car lst) u)
                      (+ (sq (car lst)) v)))))

(defthm lp17-8-lemma1
  (implies (warrant sq)
           (equal (loop$ with lst = lst0
                         with u = u0
                         with v = v0
                         do
                         (cond ((consp lst)
                                (progn (setq u (+ u (car lst)))
                                         (setq v (+ v (* (car lst) (car lst))))
                                         (setq lst (cdr lst))))
                               (t (return (cons u v)))))
                  (sum-and-sum-sq lst0 u0 v0))))

(defthm lp17-8-lemma2
  (implies (and (warrant sq)
                (acl2-numberp u0)
                (acl2-numberp v0))
           (equal (sum-and-sum-sq lst0 u0 v0)
                  (cons (+ u0 (loop$ for e in lst0 sum e))
                        (+ v0 (loop$ for e in lst0 sum (sq e)))))))

(defthm lp17-8-main
  (implies (warrant sq)
           (equal (loop$ with lst = lst
                         with u = 0
                         with v = 0
                         do
                         (cond ((endp lst) (return (cons u v)))
                               (t (progn (setq u (+ (car lst) u))
                                         (setq v (+ (sq (car lst)) v))
                                         (setq lst (cdr lst))))))
                  (cons (loop$ for e in lst sum e)
                        (loop$ for e in lst sum (sq e))))))

; -----------------------------------------------------------------
; LP17-9

; Define (partition-symbols lst) with a do loop$ that partitions lst into two
; lists, one containing all the symbols in lst and the other containing
; all the non-symbols.  Return the cons of the two partitions and prove it
; partition-symbols.

; Hint: Since you are likely to collect the elements in reverse order, a
; suitable specification for these purposes is that your loop$ is equal to

; (cons (rev (loop$ for e in lst when (symbolp e) collect e))
;       (rev (loop$ for e in lst when (not (symbolp e)) collect e)))

(defun partition-symbols (lst)
  (loop$ with lst = lst
         with syms = nil
         with non-syms = nil
         do
         (cond ((endp lst) (return (cons syms non-syms)))
               ((symbolp (car lst))
                (progn (setq syms (cons (car lst) syms))
                       (setq lst (cdr lst))))
               (t
                (progn (setq non-syms (cons (car lst) non-syms))
                       (setq lst (cdr lst)))))))

(defun recursive-partition-symbols (lst syms non-syms)
  (cond ((endp lst) (cons syms non-syms))
        ((symbolp (car lst))
         (recursive-partition-symbols (cdr lst)
                                      (cons (car lst) syms)
                                      non-syms))
        (t (recursive-partition-symbols (cdr lst)
                                        syms
                                        (cons (car lst) non-syms)))))
(defthm lp17-9-lemma1
  (equal (loop$ with lst = lst
                with syms = syms
                with non-syms = non-syms
                do
                (cond ((consp lst)
                       (cond
                        ((symbolp (car lst))
                         (progn (setq syms (cons (car lst) syms))
                                (setq lst (cdr lst))))
                        (t
                         (progn (setq non-syms (cons (car lst) non-syms))
                                (setq lst (cdr lst))))))
                      (t (return (cons syms non-syms)))))
         (recursive-partition-symbols lst syms non-syms)))

(defthm lp17-9-lemma2
  (equal (partition-symbols lst)
         (recursive-partition-symbols lst nil nil)))

(defthm lp17-9-lemma3
  (equal (recursive-partition-symbols lst syms non-syms)
         (cons (append (rev (loop$ for e in lst when (symbolp e) collect e))
                       syms)
               (append (rev (loop$ for e in lst when (not (symbolp e)) collect e))
                       non-syms))))

(defthm lp17-9-main
  (equal (partition-symbols lst)
         (cons (rev (loop$ for e in lst when (symbolp e) collect e))
               (rev (loop$ for e in lst when (not (symbolp e)) collect e)))))

; -----------------------------------------------------------------
; LP17-10

; Write a do loop$ that returns the list of naturals from n down to 0, where n
; is a natural.  For example, if n is 10 the answer is (10 9 8 7 6 5 4 3 2 1
; 0).  Prove that when n is a natural, your do loop$ returns the same thing as
; (loop$ for i from 0 to n collect (- n i)).

; Hints: Remember that in order for your lemma about the generalized do loop$
; is applied in the proof of your main theorem it must match the rewritten
; lambda objects of the main theorem.  But that means it must not only match
; the do-body lambda object.  It must also match the measure lambda object!  So
; pay special attention to the normalized measure lambda object in your
; ``lemma1.''  And by the way, if you have non-recursive functions you don't
; want opened up when the lambda objects are rewritten, try disabling them.

(defun nats-ac-up (i n ans)
  (declare (xargs :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (let ((i (nfix i))
        (n (nfix n)))
    (if (> i n)
        ans
        (nats-ac-up (+ i 1) n (cons i ans)))))

; Note the normalized measure expression!  But in addition, when it comes time
; for this lemma to fire in the proof of the main theorem, we should have nfix
; disabled or else it will open in the main theorem and scatter IFs all over
; the measure lambda!

(defthm lp17-10-lemma1
  (implies (and (natp n)
                (natp i0))
           (equal 
            (loop$ with i = i0
                   with ans = ans0
                   do
                   :measure (nfix (+ 1 (- (nfix i)) (nfix n)))
		   (if (< n i)
                       (return ans)
                       (progn (setq ans (cons i ans))
                              (setq i (+ 1 i)))))
            (nats-ac-up i0 n ans0))))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm minus-minus-n
  (implies (acl2-numberp n)
           (equal (- (- n)) n)))

(defthm lp17-10-lemma2
  (implies (and (natp n)
                (natp i0))
           (equal (nats-ac-up i0 n ans0)
                  (append (loop$ for i from 0 to (- n i0) collect (- n i))
                          ans0))))

; Note that we wrote the measure in the way it was originally written, not in
; the ``normalized'' form used in lemma1.  And we'll disable nfix in this
; proof.

(defthm lp17-10-main
  (implies (natp n)
           (equal (loop$ with i = 0
                         with ans = nil
                         do
                         :measure (nfix (- (+ 1 (nfix n)) (nfix i)))
		         (if (< n i)
                             (return ans)
                             (progn (setq ans (cons i ans))
                                    (setq i (+ 1 i)))))
                  (loop$ for i from 0 to n collect (- n i))))
  :hints (("Goal" :in-theory (disable nfix))))

; -----------------------------------------------------------------
; LP17-11

; Define (all-pairs-do-loop$ imax jmax) to compute the same (all-pairs imax
; jmax) as was defined in section 11.  But use do loop$s instead of for
; loop$s in your definition of all-pairs-do-loop$.

; Recall the definition of all-pairs.
(defun make-pair (i j)
  (declare (xargs :guard t))
  (cons i j))

(defwarrant make-pair)

(defun all-pairs-helper2 (i j jmax)
  (declare (xargs :measure (nfix (- (+ (nfix jmax) 1) (nfix j)))
                  :guard (and (natp i) (natp j) (natp jmax))))
  (let ((j (nfix j))
        (jmax (nfix jmax)))
    (cond
     ((> j jmax) nil)
     (t (cons (make-pair i j)
              (all-pairs-helper2 i (+ 1 j) jmax))))))

(defun all-pairs-helper1 (i imax jmax)
  (declare (xargs :measure (nfix (- (+ (nfix imax) 1) (nfix i)))
                  :guard (and (natp i) (natp imax) (natp jmax))))
  (let ((i (nfix i))
        (imax (nfix imax)))
    (cond
     ((> i imax) nil)
     (t (append (all-pairs-helper2 i 1 jmax)
                (all-pairs-helper1 (+ 1 i) imax jmax))))))

(defun all-pairs (imax jmax)
  (declare (xargs :guard (and (natp imax) (natp jmax))))
  (all-pairs-helper1 1 imax jmax))

; Hints: In following our advice on proving do loop$s you will define functions
; that compute the same things as your do loop$s.  These functions will suggest
; the appropriate inductions.  Your ``lemma1'' will prove your do loop$s
; compute the pairs computed by those functions.  The next step in the recipe
; is to prove that the functions compute the same thing that all-pairs does.
; This will not involve loop$s of any sort.  It's just a normal proof about the
; relation between some recursively defined functions.  But we found this step
; surprisingly challenging!

; Since that second step does not involve loop$s, you may consider your answer
; correct if you just prove lemma1!

(defun all-pairs-do-loop$ (imax jmax)
  (declare (xargs :guard (and (natp imax) (natp jmax))))
  (loop$ with i = imax
         with ans = nil
         do
         :guard (and (natp i) (natp jmax))
         (cond
          ((< i 1)
           (return ans))
          (t (progn
               (setq ans (loop$ with j = jmax
                                with ans = ans
                                do
                                :guard (natp j)
                                (cond
                                 ((< j 1)
                                  (return ans))
                                 (t (progn
                                      (setq ans (cons (make-pair i j) ans))
                                      (setq j (- j 1)))))))
               (setq i (- i 1)))))))

; By the way, all three of the :guards can be deleted and this proof will still
; work.  The guards are important only if we mean to run fast code in raw Lisp.
; We don't really care about fast code in this exercise, but we leave the
; guards in place below as an illustration of guards.

; The next job is to prove that the above function computes all-pairs.
; However, all-pairs recurs ``up'' while our do loop$s recur ``down.''  So
; first we'll define versions of all-pairs that recur down.  These functions
; serve dual roles here.  First, they provide the induction hint.  Second, they
; provide an intermediate specification.  That is, inducting according to the
; functions below let us prove that the do loop$s are equal to the functions
; below.  Later we'll prove that these functions are ``equal'' to
; all-pairs-helper2 and all-pairs-helper1.

; By the way, ``apdh'' is an abbreviation for ``all-pairs-do-helper.''

(defun apdh2 (i j ans)
  (cond
   ((natp j)
    (cond ((< j 1) ans)
          (t (apdh2 i (- j 1) (cons (make-pair i j) ans)))))
   (t nil)))

(defun apdh1 (i jmax ans)
  (cond
   ((natp i)
    (cond ((< i 1) ans)
          (t (apdh1 (- i 1) jmax (apdh2 i jmax ans)))))
   (t nil)))

; We start with the proof that the inner loop is apdh2.  But note that we've
; normalized the body of the loop$ so that it will match the rewritten loop$
; body in the next theorem.  Normalizing here just means we expand the
; non-recursive function make-pair.  This expansion coincidentally eliminates
; the need for the warrant for make-pair, at least in the proof of this lemma.

(defthm lp17-11-adph2-lemma1
  (implies (natp jmax)                              ; <--- no warrant req'd
           (equal                                   ;      because no make-
            (loop$ with j = jmax                    ;      pair anymore
                   with ans = ans0
                   do
                   :guard (natp j)
                   (cond
                    ((< j 1)
                     (return ans))
                    (t (progn
                         (setq ans (cons (cons i j) ; <--- make-pair opened
                                         ans))
                         (setq j (- j 1))))))
            (apdh2 i jmax ans0))))

; Prove that the generalized outer loop$ is apdh1.
(defthm lp17-11--adph1-lemma1
  (implies
   (and (warrant do$)                             ; <--- no warrant make-pair
        (natp imax)
        (natp jmax))
   (equal
    (loop$ with i = imax
           with ans = ans0                        ; <--- ans0 instead of nil
           do
           :guard (and (natp i) (natp jmax))
           (cond
            ((< i 1)
             (return ans))
            (t (progn
                 (setq ans (loop$ with j = jmax   ; <--- normalized inner
                                  with ans = ans  ;      loop$
                                  do
                                  :guard (natp j)
                                  (cond
                                   ((< j 1)
                                    (return ans))
                                   (t (progn
                                        (setq ans (cons (cons i j) ans))
                                        (setq j (- j 1)))))))
                 (setq i (- i 1))))))
    (apdh1 imax jmax ans0))))

(defthm lp17-11-main--sort-of
  (implies (and (warrant do$ make-pair)
                (natp imax)
                (natp jmax))
           (equal (all-pairs-do-loop$ imax jmax)
                  (apdh1 imax jmax nil))))

; We could declare victory here, according to the hint given in the problem
; statement.  We proved our all-pairs-do-loop$ computes the same thing as
; adph1.  But the problem actually said prove it equal to all-pairs but said
; we'd accept the above as a correct answer.  We'll carry on to the final
; result.

; We disable all-pairs-do-loop$ because from here on we'll just deal with the
; equivalent (apdh1 imax jmax nil).

(in-theory (disable all-pairs-do-loop$))

; It remains to prove that apdh1 is the same as all-pairs.  That has nothing to
; do with loop$.  It's actually a fairly non-elementary proof.  We relegate it
; a subsidary book since it's not about loops.  The book below proves ``lemma2''
; for apdh2 and apdh1, which allows us to finish the proof of main.

(include-book "lp17-11-lemma2")

; But since all-pairs-do-loop$ rewrites to apd1 (with ans = nil) and all-pairs rewrites
; to all-pairs-helper1, we're done:

(defthm lp17-11-main
  (implies (and (warrant do$ make-pair)
                (natp imax)
                (natp jmax))
           (equal (all-pairs-do-loop$ imax jmax)
                  (all-pairs imax jmax))))
