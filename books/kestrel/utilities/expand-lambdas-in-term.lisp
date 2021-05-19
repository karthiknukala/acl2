; Utilities for expanding lambdas
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "substitution")
(include-book "lambda-free-termp")
(include-book "lambdas-closed-in-termp")
(local (include-book "../alists-light/pairlis-dollar"))
(local (include-book "../alists-light/strip-cars"))
(local (include-book "../lists-light/subsetp-equal"))
(local (include-book "../typed-lists-light/symbol-listp"))

;; Substitution doesn't introduce lambdas if there were none to start with and
;; there are none in the alist being used for substitution.
(defthm-flag-my-sublis-var
  (defthm lambda-free-termp-of-my-sublis-var
    (implies (and (lambda-free-termp form)
                  (lambda-free-termsp (strip-cdrs alist)))
             (lambda-free-termp (my-sublis-var alist form)))
    :flag my-sublis-var)
  (defthm lambda-free-termsp-of-my-sublis-var-lst
    (implies (and (lambda-free-termsp l)
                  (lambda-free-termsp (strip-cdrs alist)))
             (lambda-free-termsp (my-sublis-var-lst alist l)))
    :flag my-sublis-var-lst)
  :hints (("Goal" :in-theory (enable my-sublis-var
                                     my-sublis-var-lst))))

;; Expands away all lambdas in TERM (beta reduction).  This is similar to the
;; built-in function REMOVE-LAMBDAS, but that one does more (to preserve quote
;; normal form). For example: (remove-lambdas '((lambda (x y) (binary-+ x y))
;; '1 '2)) produces '3 whereas we want (binary-+ '1 '2).
(mutual-recursion
 (defund expand-lambdas-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (expand-lambdas-in-terms args)) ;process the args first
            (fn (ffn-symb term)))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((lambda-body (expand-lambdas-in-term (lambda-body fn)))) ;;apply recursively to the lambda body
             ;; beta-reduce (TODO: Make a simple version of subcor-var and call that here):
             (my-sublis-var (pairlis$ (lambda-formals fn) args) lambda-body))
         ;;not a lambda application, so just rebuild the function call:
         `(,fn ,@args)))))

 (defund expand-lambdas-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (expand-lambdas-in-term (first terms))
           (expand-lambdas-in-terms (rest terms))))))

(make-flag expand-lambdas-in-term)

;TODO: Automate some of this?

(defthm len-of-expand-lambdas-in-terms
  (equal (len (expand-lambdas-in-terms terms))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable len expand-lambdas-in-terms))))

(defthm consp-of-expand-lambdas-in-terms
  (equal (consp (expand-lambdas-in-terms terms))
         (consp terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable len expand-lambdas-in-terms))))

;; Expanding lambdas preserves pseudo-termp.
(defthm-flag-expand-lambdas-in-term
  (defthm pseudo-termp-of-expand-lambdas-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (expand-lambdas-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm pseudo-term-listp-of-expand-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (expand-lambdas-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :in-theory (enable expand-lambdas-in-term
                                     expand-lambdas-in-terms))))

(verify-guards expand-lambdas-in-term)

(defthm car-of-expand-lambdas-in-terms
  (equal (car (expand-lambdas-in-terms terms))
         (expand-lambdas-in-term (car terms)))
  :hints (("Goal" :in-theory (enable expand-lambdas-in-terms))))

;; Expanding lambdas creates a lambda-free term.
(defthm-flag-expand-lambdas-in-term
  (defthm lambda-free-termp-of-expand-lambdas-in-term
    (implies (pseudo-termp term)
             (lambda-free-termp (expand-lambdas-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm lambda-free-term-listp-of-expand-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (lambda-free-termsp (expand-lambdas-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :in-theory (enable expand-lambdas-in-term
                                     expand-lambdas-in-terms))))

;; Since the new term is lambda-free
(defthm not-consp-of-car-of-expand-lambdas-in-term
  (implies (pseudo-termp term)
           (not (consp (car (expand-lambdas-in-term term)))))
  :hints (("Goal" :use (:instance lambda-free-termp-of-expand-lambdas-in-term)
           :in-theory (disable lambda-free-termp-of-expand-lambdas-in-term))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-assoc-equal-and-free-vars-in-terms-of-strip-cdrs
   (implies (and (member-equal term (strip-cars alist))
                 (assoc-equal term alist))
            (subsetp-equal (free-vars-in-term (cdr (assoc-equal term alist)))
                           (free-vars-in-terms (strip-cdrs alist))))
   :hints (("Goal" :in-theory (enable subsetp-equal assoc-equal free-vars-in-terms)))))

;move
(defthm-flag-free-vars-in-term
  (defthm subsetp-equal-of-free-vars-in-term-of-my-sublis-var-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-term term)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-term (my-sublis-var alist term))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-term)
  (defthm subsetp-equal-of-free-vars-in-term-of-my-sublis-var-lst-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-terms terms)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-terms (my-sublis-var-lst alist terms))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable my-sublis-var
                                     my-sublis-var-lst
                                     free-vars-in-term
                                     free-vars-in-terms))))

;; Expanding lambdas doesn't introduce new free vars (assuming lambdas are
;; closed).  Note that expanding lambdas can remove free vars, since some
;; lambda formals may not appear in the lambda body (so their actuals are
;; effectively dropped).
(defthm-flag-expand-lambdas-in-term
  (defthm subsetp-equal-of-free-vars-in-term-of-expand-lambdas-in-term-and-free-vars-in-term
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                            (free-vars-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm subsetp-equal-of-free-vars-in-terms-of-expand-lambdas-in-terms-and-free-vars-in-terms
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (subsetp-equal (free-vars-in-terms (expand-lambdas-in-terms terms))
                            (free-vars-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints ( ("subgoal *1/2" :use (:instance subsetp-equal-of-free-vars-in-term-of-my-sublis-var-and-free-vars-in-terms-of-strip-cdrs
                                           (term (expand-lambdas-in-term (caddr (car term))))
                                           (alist (pairlis$ (cadr (car term))
                                                            (expand-lambdas-in-terms (cdr term))))))
           ("Goal" :in-theory (e/d (free-vars-in-term
                                    expand-lambdas-in-term
                                    expand-lambdas-in-terms
                                    lambdas-closed-in-termp)
                                   (subsetp-equal-of-free-vars-in-term-of-my-sublis-var-and-free-vars-in-terms-of-strip-cdrs)))))
