; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "gl-object")
(include-book "constraint-inst")

(local (include-book "scratchobj"))

(local (std::add-default-post-define-hook :fix))



;; This book defines a stack containing "major frames", each containing a stack
;; of "minor frames".  Each major and minor frame contains a binding alist and
;; perhaps some debug info.  The complete set of bindings at a given point in
;; symbolic execution is the local minor frame bindings appended to the local
;; major frame bindings.  Each minor frame also contains a scratch
;; stack, which is a stack of objects of various types.

;; This two-dimensional nesting approach supports the style of symbolic
;; execution we do in GL, specifically late binding of free variables in hyps
;; and RHSes of rules (used for an extension of syntaxp/bind-free).

;; Major stack frames correspond to places in symbolic execution where we enter
;; an entirely new namespace, such as when we enter the body of a function or
;; begin relieving the hyps/executing the RHS of a rewrite rule under the
;; unification substitution.

;; Minor stack frames correspond essentially to entries into lambda bodies.
;; Except, we process nestings of lambdas into bindinglists (see
;; centaur/meta/bindinglist) so that if a lambda call is nested directly inside
;; a lambda body, we reuse the outer frame.  In classical ACL2, each lambda
;; binds all the variables that are used in its body and so a lambda body is in
;; its very own namespace.  However, when we process lambdas into bindinglists,
;; we throw out variables that are bound to themselves, and compensate by
;; appending the new bindings to the existing bindings.  This helps to support
;; late bindings by allowing us to leave variables unbound until they are
;; "really used", that is, passed into a function or bound to a different
;; variable in a lambda.

;; A stack has one or more major stack frames.  A major stack frame has a base
;; binding list, a debug area, and one or more minor stack frames.  A minor
;; stack frame has a binding list, two scratch lists: one for gl-objects and
;; one for BFRs, and a debug area.

;; See stack.lisp for the stobj implementation of the stack.



(make-event
 `(progn
    (fty::deftagsum scratchobj
      :layout :tree
      . ,(acl2::template-proj '(:<kind> ((val <pred> . <ruleclass>)))
                              *scratchobj-tmplsubsts*))

    (defenum scratchobj-kind-p ,(acl2::template-proj :<kind> *scratchobj-tmplsubsts*))

    (defthm scratchobj-kind-p-of-scratchobj-kind
      (scratchobj-kind-p (scratchobj-kind x))
      :hints(("Goal" :in-theory (enable scratchobj-kind))))))

(make-event
 `(progn
    (define scratchobj-kind->code ((x scratchobj-kind-p))
      :returns (code natp :rule-classes :type-prescription)
      (case x
        ,@(acl2::template-proj '(:<kindcase> <code>) *scratchobj-tmplsubsts*))
      ///
      (local (in-theory (enable scratchobj-kind-fix)))

      (defret unsigned-byte-p-of-<fn>
        (unsigned-byte-p 4 code)))

    (define scratchobj-code->kind ((x natp))
      :returns (kind scratchobj-kind-p)
      (case (lnfix x)
        ,@(acl2::template-proj '(<codecase> :<kind>) *scratchobj-tmplsubsts*))
      ///
      (defthm scratchobj-code->kind-of-scratchobj-kind->code
        (equal (scratchobj-code->kind (scratchobj-kind->code kind))
               (scratchobj-kind-fix kind))
        :hints(("Goal" :in-theory (enable scratchobj-kind->code scratchobj-kind-fix)))))))



(fty::deflist scratchlist :elt-type scratchobj :true-listp t)

(fty::defprod minor-frame
  ((bindings gl-object-bindings-p)
   (scratch scratchlist-p)
   (debug)))

(fty::deflist minor-stack :elt-type minor-frame :true-listp t :non-emptyp t
  ///
  (defthm minor-stack-p-of-cons-cdr
    (implies (and (minor-stack-p x)
                  (minor-frame-p a))
             (minor-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable minor-stack-p)))))

(make-event
 `(fty::defprod major-frame
    ((bindings gl-object-bindings-p)
     (debug)
     (minor-stack minor-stack-p :default ',(list (make-minor-frame))))))

(fty::deflist major-stack :elt-type major-frame :true-listp t :non-emptyp t
  ///
  (defthm major-stack-p-of-cons-cdr
    (implies (and (major-stack-p x)
                  (major-frame-p a))
             (major-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable major-stack-p)))))




(define stack$a-frames ((x major-stack-p))
  (len (major-stack-fix x)))

(define stack$a-push-frame ((x major-stack-p))
  :returns (stack major-stack-p)
  (cons (make-major-frame) (major-stack-fix x)))

(define stack$a-minor-frames ((x major-stack-p))
  (len (major-frame->minor-stack (car x))))

(define stack$a-push-minor-frame ((x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix
     (cons (change-major-frame jframe :minor-stack
                               (cons (make-minor-frame) jframe.minor-stack))
           (cdr x)))))

(define stack$a-set-bindings ((bindings gl-object-bindings-p)
                              (x major-stack-p))
  :returns (stack major-stack-p)  
  (major-stack-fix (cons (change-major-frame (car x) :bindings bindings)
                         (cdr x))))

(define stack$a-add-binding ((var pseudo-var-p)
                             (val gl-object-p)
                             (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame frame) (car x)))
    (major-stack-fix (cons (change-major-frame frame :bindings (cons (cons (pseudo-var-fix var)
                                                                           (gl-object-fix val))
                                                                     frame.bindings))
                           (cdr x)))))

(define stack$a-set-debug (debug
                           (x major-stack-p))
  :returns (stack major-stack-p)
  (major-stack-fix (cons (change-major-frame (car x) :debug debug)
                         (cdr x))))


(local (defthm gl-object-bindings-p-of-append
           (implies (and (gl-object-bindings-p x)
                         (gl-object-bindings-p y))
                    (gl-object-bindings-p (append x y)))))

(define stack$a-set-minor-bindings ((bindings gl-object-bindings-p)
                                    (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :bindings bindings)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-add-minor-bindings ((bindings gl-object-bindings-p)
                                    (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :bindings (append bindings nframe.bindings))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(define stack$a-set-minor-debug ((debug)
                                 (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :debug debug)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-bindings ((x major-stack-p))
  :returns (binings gl-object-bindings-p)
  (major-frame->bindings (car x)))


(define stack$a-minor-bindings ((x major-stack-p))
  :returns (binings gl-object-bindings-p)
  (minor-frame->bindings (car (major-frame->minor-stack (car x)))))


(define stack$a-debug ((x major-stack-p))
  (major-frame->debug (car x)))


(define stack$a-minor-debug ((x major-stack-p))
  (minor-frame->debug (car (major-frame->minor-stack (car x)))))


(define stack$a-scratch-len ((x major-stack-p))
  (len (minor-frame->scratch (car (major-frame->minor-stack (car x))))))


(define stack$a-top-scratch ((x major-stack-p))
  :guard (< 0 (stack$a-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-scratch-len)))
  :returns (obj scratchobj-p)
  (scratchobj-fix (car (minor-frame->scratch (car (major-frame->minor-stack (car x)))))))

(define stack$a-nth-scratch ((n natp)
                             (x major-stack-p))
  :guard (< n (stack$a-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-scratch-len)))
  :returns (obj scratchobj-p)
  (scratchobj-fix (nth n (minor-frame->scratch (car (major-frame->minor-stack (car x)))))))


(define stack$a-pop-scratch ((x major-stack-p))
  :guard (< 0 (stack$a-scratch-len x))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch
                                                                         (cdr nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-pop-multi-scratch ((n natp)
                                   (x major-stack-p))
  :guard (< n (stack$a-scratch-len x))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch
                                                                         (nthcdr n nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(define stack$a-push-scratch ((obj scratchobj-p)
                              (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack))) 
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch (cons
                                                                                   obj
                                                                                   nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(fty::deffixcong scratchobj-equiv scratchlist-equiv (update-nth n v x) v)

(define stack$a-update-scratch ((n natp)
                                (obj scratchobj-p)
                                (x major-stack-p))
  :returns (stack major-stack-p)
  :guard (< n (stack$a-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-scratch-len)))
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack))) 
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch (update-nth n
                                                                                              obj
                                                                                              nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(local
 (progn
   (defconst *scratchobj-template*
     '(progn (define stack$a-push-scratch-<kind> ((obj <pred>)
                                                  (x major-stack-p))
               :returns (stack major-stack-p)
               :enabled t
               (stack$a-push-scratch (scratchobj-<kind> obj) x))

             (define stack$a-top-scratch-<kind> ((x major-stack-p))
               :guard (and (< 0 (stack$a-scratch-len x))
                           (scratchobj-case (stack$a-top-scratch x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-top-scratch)))
               :returns (obj <pred>)
               :enabled t
               (scratchobj-<kind>->val (stack$a-top-scratch x)))

             (define stack$a-nth-scratch-<kind> ((n natp)
                                                 (x major-stack-p))
               :guard (and (< n (stack$a-scratch-len x))
                           (scratchobj-case (stack$a-nth-scratch n x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-nth-scratch)))
               :returns (obj <pred>)
               :enabled t
               (scratchobj-<kind>->val (stack$a-nth-scratch n x)))

             (define stack$a-update-scratch-<kind> ((n natp)
                                                    (obj <pred>)
                                                    (x major-stack-p))
               :guard (< n (stack$a-scratch-len x))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-nth-scratch)))
               :returns (stack major-stack-p)
               :enabled t
               (stack$a-update-scratch n (scratchobj-<kind> obj) x))

             (define stack$a-pop-scratch-<kind> ((x major-stack-p))
               :guard (and (< 0 (stack$a-scratch-len x))
                           (scratchobj-case (stack$a-top-scratch x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-top-scratch)))
               :enabled t
               (mv (stack$a-top-scratch-<kind> x)
                   (stack$a-pop-scratch x)))))))

(make-event
 (cons 'progn (acl2::template-proj *scratchobj-template*
                                   *scratchobj-tmplsubsts*)))









(local (defthm len-gt-0
         (equal (< 0 (len x))
                (consp x))))

(local (defthm <-cancel
         (implies (syntaxp (and (quotep c1) (quotep c2)))
                  (equal (< c1 (+ c2 x))
                         (< (- c1 c2) (fix x))))
         :hints (("goal" :Cases ((< c1 (+ c2 x)))))))

(define stack$a-pop-minor-frame ((x major-stack-p))
  :guard (and (< 1 (stack$a-minor-frames x))
              (eql (stack$a-scratch-len x) 0))
  :guard-hints (("goal" :in-theory (enable stack$a-minor-frames)))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack (cdr jframe.minor-stack))
                           (cdr x)))))

(define stack$a-pop-frame ((x major-stack-p))
  :guard (and (< 1 (stack$a-frames x))
              (eql 1 (stack$a-minor-frames x))
              (eql 0 (stack$a-scratch-len x)))
  :guard-hints (("goal" :in-theory (enable stack$a-frames)))
  :returns (stack major-stack-p)
  (major-stack-fix (cdr x)))

(define stack$a-extract ((x major-stack-p))
  :enabled t
  (major-stack-fix x))





(define create-stack$a ()
  :enabled t
  :returns (stack major-stack-p)
  (list (make-major-frame)))









;; BOZO Unfortunately scratchobj-bfrlist is the constructor for the bfrlist
;; kind of scratchobj so we use an unconventional name.
(define scratchobj->bfrlist ((x scratchobj-p))
  :returns (bfrs)
  (scratchobj-case x
    :gl-obj (gl-object-bfrlist x.val)
    :gl-objlist (gl-objectlist-bfrlist x.val)
    :bfr (list x.val)
    :bfrlist x.val
    :cinst (constraint-instance-bfrlist x.val)
    :cinstlist (constraint-instancelist-bfrlist x.val))
  ///
  (local (include-book "scratchobj"))
  (make-event
   `(defthm scratchobj->bfrlist-of-make-scratchobjs
      (and ,@(acl2::template-proj
              '(equal (scratchobj->bfrlist (scratchobj-<kind> x))
                      (<prefix>-bfrlist x))
              (scratchobj-tmplsubsts (acl2::remove-assoc
                                      :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*))))
           (equal (scratchobj->bfrlist (scratchobj-bfr x)) (list x))
           (equal (scratchobj->bfrlist (scratchobj-bfrlist x)) (true-list-fix x)))))

  (deffixequiv scratchobj->bfrlist)

  (make-event
   (cons 'progn
         (acl2::template-proj
          '(defthm bfrlist-of-scratchobj-<kind>->val
             (implies (scratchobj-case x :<kind>)
                      (equal (<prefix>-bfrlist (scratchobj-<kind>->val x))
                             (scratchobj->bfrlist x))))
          (scratchobj-tmplsubsts (acl2::remove-assoc
                                  :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*))))))

  (defthm bfrlist-of-scratchobj-bfr->val
    (implies (and (not (member v (scratchobj->bfrlist x)))
                  (scratchobj-case x :bfr))
             (not (equal v (scratchobj-bfr->val x)))))

  (defthm bfrlist-of-scratchobj-bfrlist->val
    (implies (and (not (member v (scratchobj->bfrlist x)))
                  (scratchobj-case x :bfrlist))
             (not (member v (scratchobj-bfrlist->val x))))))

  

(define scratchlist-bfrlist ((x scratchlist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (scratchobj->bfrlist (car x))
            (scratchlist-bfrlist (cdr x))))
  ///
  (defthm scratchlist-bfrlist-of-cons
    (equal (scratchlist-bfrlist (cons a b))
           (append (scratchobj->bfrlist a)
                   (scratchlist-bfrlist b))))

  (defthm scratchobj->bfrlist-of-car
    (implies (not (member v (scratchlist-bfrlist x)))
             (not (member v (scratchobj->bfrlist (car x))))))

  (defthm scratchlist-bfrlist-of-car
    (implies (not (member v (scratchlist-bfrlist x)))
             (not (member v (scratchlist-bfrlist (cdr x)))))))

(define minor-frame-bfrlist ((x minor-frame-p))
  :returns (bfrs)
  (b* (((minor-frame x)))
    (append (gl-object-bindings-bfrlist x.bindings)
            (scratchlist-bfrlist x.scratch)))
  ///
  (defthm minor-frame-bfrlist-of-minor-frame
    (equal (minor-frame-bfrlist (minor-frame bindings scratch debug))
           (append (gl-object-bindings-bfrlist bindings)
                   (scratchlist-bfrlist scratch))))

  (defthm bfrlist-of-minor-frame->bindings
    (implies (not (member v (minor-frame-bfrlist x)))
             (not (member v (gl-object-bindings-bfrlist (minor-frame->bindings x))))))

  (defthm bfrlist-of-minor-frame->scratch
    (implies (not (member v (minor-frame-bfrlist x)))
             (not (member v (scratchlist-bfrlist (minor-frame->scratch x)))))))

(define minor-stack-bfrlist ((x minor-stack-p))
  :returns (bfrs)
  :ruler-extenders (binary-append)
  (append (minor-frame-bfrlist (car x))
          (and (consp (cdr x))
               (minor-stack-bfrlist (cdr x))))
  ///
  (defthm minor-stack-bfrlist-of-cons
    (equal (minor-stack-bfrlist (cons a b))
           (append (minor-frame-bfrlist a)
                   (minor-stack-bfrlist b))))

  (defthm minor-frame-bfrlist-of-car
    (implies (not (member v (minor-stack-bfrlist x)))
             (not (member v (minor-frame-bfrlist (car x))))))

  (defthm minor-stack-bfrlist-of-car
    (implies (not (member v (minor-stack-bfrlist x)))
             (not (member v (minor-stack-bfrlist (cdr x)))))))

(define major-frame-bfrlist ((x major-frame-p))
  :returns (bfrs)
  (b* (((major-frame x)))
    (append (gl-object-bindings-bfrlist x.bindings)
            (minor-stack-bfrlist x.minor-stack)))
  ///
  (defthm major-frame-bfrlist-of-major-frame
    (equal (major-frame-bfrlist (major-frame bindings debug minor-stack))
           (append (gl-object-bindings-bfrlist bindings)
                   (minor-stack-bfrlist minor-stack))))

  (defthm bfrlist-of-major-frame->bindings
    (implies (not (member v (major-frame-bfrlist x)))
             (not (member v (gl-object-bindings-bfrlist (major-frame->bindings x))))))

  (defthm bfrlist-of-major-frame->minor-stack
    (implies (not (member v (major-frame-bfrlist x)))
             (not (member v (minor-stack-bfrlist (major-frame->minor-stack x)))))))

(define major-stack-bfrlist ((x major-stack-p))
  :returns (bfrs)
  :ruler-extenders (binary-append)
  (append (major-frame-bfrlist (car x))
          (and (consp (cdr x))
               (major-stack-bfrlist (cdr x))))
  ///
  (defthm major-stack-bfrlist-of-cons
    (equal (major-stack-bfrlist (cons a b))
           (append (major-frame-bfrlist a)
                   (major-stack-bfrlist b))))

  (defthm major-frame-bfrlist-of-car
    (implies (not (member v (major-stack-bfrlist x)))
             (not (member v (major-frame-bfrlist (car x))))))

  (defthm major-stack-bfrlist-of-car
    (implies (not (member v (major-stack-bfrlist x)))
             (not (member v (major-stack-bfrlist (cdr x)))))))