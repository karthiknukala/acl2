; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>


(in-package "VL")

(include-book "scopestack")
(include-book "centaur/sv/svex/svex" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable acl2::consp-under-iff-when-true-listp)))

(defxdoc elabindex
  :parents (elaborate)
  :short "A data structure for recording elaboration results, i.e., functions,
types, and parameters."
  :long "
<h3>Basic Usage</h3>
<ul>
<li>@(see vl-elabindex-init) initializes an empty elabindex at the design scope.</li>
<li>@(see vl-elabindex-update-item-info) adds an entry about a parameter, type, or function name to the current scope.</li>
<li>@(see vl-elabindex-traverse-to-ss) traverses to the scope represented by the given scopestack.</li>
<li>@(see vl-elabindex-push) enters the given scope.</li>
<li>@(see vl-elabindex-undo) undoes the latest traversal/push that hasn't already been undone.</li>
<li>@(see vl-elabindex->ss) accesses the scopestack of the current location</li>
<li>@(see vl-elabindex->scopes) accesses the stack of elabinfo scopes for the current location.</li>
</ul>

<p>An elabindex is most useful when you are going to be adding new elaboration
results.  To simply examine elaboration results, you may use a @(see
vl-elabscope-stack).  This is a data structure used in an elabindex, but also
has a set of functions appropriate for using it in an applicative manner.</p>


<h3>Introduction</h3>
<p>One of the biggest difficulties in processing SystemVerilog is the
complicated dependencies among functions, parameters, and types.  There is no
way to unravel these dependencies so that we can (e.g.) resolve parameter
values first, then types, then function definitions: in fact, each of these can
depend on all the others.  So they must all be processed in one step, so that
if a parameter depends on a function definition, we can go and resolve that
function definition, which may depend on other parameters and types, before
coming back to the original parameter with the function's resolved definition.</p>

<p>The step that resolves all of these is called elaboration.  During
elaboration, we unparameterize modules and traverse the design in order to
resolve types and replace constant expressions with their values where
possible.  Elaboration is complicated by the fact that there is no set order
for dependencies; we must be able to go look up an arbitrary
parameter/function/type anywhere in the module and resolve it before
continuing.</p>

<p>This style of traversal is difficult for our applicative-style data
structures; when we go to a different part of the design, resolve something,
and come back to another part of the design, it is expensive to record the
result that we obtained in the design, especially since it has been
processed (e.g.) a scopestack.</p>

<p>An elabindex is our solution to this problem.  It is designed to allow us to
efficiently record and look up results while performing both treelike and
non-treelike traversals of the design.</p>

<h3>Implementation</h3>

<p>An elabindex contains a scopestack and an elabscope-stack.  A scopestack
contains all the smarts necessary to look up items correctly (which can be
nontrivial when you factor in imports, etc.).  The elabscope-stack contains
analogous scopes as the scopestack, but these scopes record elaboration
information and are designed to be easily updated, as well as the subscopes
contained within.  To make writes to a scope permanent, each time we go up a
scope, we pop the scope off of the elabscope-stack, but write it into the
parent scope so that next time we go into that scope, we'll get our most recent
updates.</p>

<p>An exception to this: Some scopes are anonymous, e.g., a block statement
inside an always block.  Such a scope can't be accessed by name from within the
surrounding context -- it can only be reached through a treelike traversal,
i.e., processing all the always blocks in a module.  When going up in scope
from some such a scope, we don't write it to the parent scope because it
doesn't have a name to index it by.</p>

<p>A tricky use case: Suppose we are working in some anonymous scope, e.g., a
block statement inside an always. Such a scope can't be accessed by name from
within the surrounding context -- it can only be reached through a treelike
traversal, i.e., processing all the always blocks in a module.  Then, suppose
we need to look up some parameter located in a package.  We need to go into
that parameter's context to compute its value, then pop back to our previous
context.</p>

<p>How can we accomplish this?  Some ideas and their flaws:</p>

<ul>

<li>Keep a stack of checkpoints, i.e. before going to the package context, save
our current elabscope-stack, and restore it when we're done computing the
parameter.  Problem: we need to save the work we did to compute the parameter,
so we can't just revert to our previous elabscope-stack.</li>

<li>Keep a stack of paths that uniquely identify the current location.  When
going to a new location, push the current location's path onto the stack, and
when we want to come back to it, pop it off and navigate back to it.  Problem:
anonymous scopes don't have names.  Also, going back to the top of the design
to follow a path from the beginning might be inefficent -- we might even
traverse to the same scope we were already in.  Since popping scopes involves
writing to a fast alist, we don't want to do this unnecessarily.</li>

</ul>

<p>Our actual implementation:</p>

<p>Keep a stack of traversal instructions that say how to get back to the
previous scope from the scope you reached.  Each such traversal is a sequence
of instructions, where each instruction is one of:</p>

<ul>
<li>Go up a scope</li>
<li>Go down into the scope of some name</li>
<li>Go down into this anonymous scope (where the scope itself is part of the
instruction).</li>
</ul>

<p>Distinguishing between named and anonymous scopes in this way allows named
scopes to be updated via \"random access\", i.e. following
parameter/function/type dependencies.  Anonymous scopes don't need to be
updated this way because parameter/function/type dependencies won't take you
back to one.  (An exception, arguably, is a block scope inside a function
definition.  But this should only matter if the function calls itself
recursively, which we don't support for now anyway.)</p>")


(deftagsum vl-elabinfo
  (:function ((body  sv::svex)
              (ports vl-portdecllist)
              (type  vl-datatype)))
  (:type    ((type vl-datatype))
   :short "used for both typedefs and type parameters")
  (:param   ((type vl-datatype)
             (value-expr vl-expr)
             (value-sv   sv::svex)))
  :measure (two-nats-measure (acl2-count x) 0))

(fty::defalist vl-elabinfo-alist :key-type stringp :val-type vl-elabinfo
  :measure (two-nats-measure (acl2-count x) 0))

(defoption vl-maybe-elabinfo vl-elabinfo)

(deftagsum vl-elabkey
  (:package ((name stringp)) :hons t)
  (:item    ((name stringp)) :hons t)
  (:def     ((name stringp)) :hons t)
  :layout :tree)

(defoption vl-maybe-elabkey vl-elabkey)


(deftypes vl-elabscope
  
  (fty::defalist vl-elabscope-alist :key-type vl-elabkey :val-type vl-elabscope
    :measure (two-nats-measure (acl2-count x) 0))

  (defprod vl-elabscope
    ((subscopes vl-elabscope-alist)
     (members vl-elabinfo-alist))
    :measure (two-nats-measure (acl2-count x) 1)))


(defines vl-elabscope-clean
  (define vl-elabscope-alist-clean ((x vl-elabscope-alist-p)
                                    (acc vl-elabscope-alist-p))
    :returns (res vl-elabscope-alist-p)
    :measure (vl-elabscope-alist-count x)
    :verify-guards nil
    (b* ((x (vl-elabscope-alist-fix x))
         (acc (vl-elabscope-alist-fix acc))
         ((when (atom x)) acc)
         ((cons key val) (car x))
         ((when (hons-get key acc))
          (vl-elabscope-alist-clean (cdr x) acc))
         (val (vl-elabscope-clean val)))
      (vl-elabscope-alist-clean (cdr x) (hons-acons key val acc))))
  (define vl-elabscope-clean ((x vl-elabscope-p))
    :returns (res vl-elabscope-p)
    :measure (vl-elabscope-count x)
    (b* (((vl-elabscope x))
         (- (fast-alist-free x.members)
            (fast-alist-free x.subscopes))
         (members (fast-alist-clean x.members))
         (subscopes (vl-elabscope-alist-clean x.subscopes nil)))
      (change-vl-elabscope x :members members :subscopes subscopes)))
  ///
  (verify-guards vl-elabscope-alist-clean))

(defthm cdr-hons-assoc-equal-of-vl-elabscope-alist-p
  (implies (vl-elabscope-alist-p x)
           (iff (cdr (hons-assoc-equal k x))
                (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable vl-elabscope-alist-p)
          :induct (len x))))

(defthm cdr-hons-assoc-equal-of-vl-elabinfo-alist-p
  (implies (vl-elabinfo-alist-p x)
           (iff (cdr (hons-assoc-equal k x))
                (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable vl-elabinfo-alist-p)
          :induct (len x))))


(define vl-elabscope-subscope ((key vl-elabkey-p) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (cdr (hons-get (vl-elabkey-fix key) (vl-elabscope->subscopes x))))

(define vl-elabscope-package-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-package name) x))

(define vl-elabscope-def-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-def name) x))

(define vl-elabscope-item-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-item name) x))

(define vl-elabscope-item-info ((name stringp) (x vl-elabscope-p))
  :returns (info (and (iff (vl-elabinfo-p info) info)
                      (vl-maybe-elabinfo-p info))
                 :hints(("Goal" :in-theory (enable vl-maybe-elabinfo-p))))
  (cdr (hons-get (string-fix name) (vl-elabscope->members x))))


(define vl-elabscope-update-subscope ((key vl-elabkey-p) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (change-vl-elabscope
   x
   :subscopes (hons-acons (vl-elabkey-fix key)
                          (vl-elabscope-fix val)
                          (vl-elabscope->subscopes x))))

(define vl-elabscope-update-subscope? ((key vl-elabkey-p) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (if (hons-equal (vl-elabscope-subscope key x) (vl-elabscope-fix val))
      (vl-elabscope-fix x)
    (vl-elabscope-update-subscope key val x)))
  

(define vl-elabscope-update-package-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-package name) val x))



(define vl-elabscope-update-def-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-def name) val x))

(define vl-elabscope-update-item-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-item name) val x))

(define vl-elabscope-update-item-info ((name stringp) (val vl-elabinfo-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (change-vl-elabscope
   x
   :members (hons-acons (string-fix name)
                        (vl-elabinfo-fix val)
                        (vl-elabscope->members x))))




(fty::defalist vl-elabscopes
  :key-type vl-maybe-elabkey
  :val-type vl-elabscope
  :true-listp t
  :short "Representation for a stack of scopes, providing read-only access to elaboration info."
  :long "<p>Elabscopes are useful for providing \"read-only\" (applicative)
access to elaboration information, e.g. once elaboration is over or once all
elaboration info necessary for some purpose has been computed.  For a structure
that supports adding in new elaboration info, use an @(see elabindex)
stobj.</p>

<h3>Interface</h3>

<ul>
<li>@(see vl-elabscopes-init) creates a new elabscopes at the design level.</li>
<li>@(see vl-elabscopes-push-scope) enters a scope inside the current one.</li>
<li>@(see vl-elabscopes-pop) pops out @('n') scope levels.</li>
<li>@(see vl-elabscopes-root) pops out to the root (global) scope.</li>
<li>@(see vl-elabscopes-traverse) enters the scope specified by a
traversal (returned by certain utilies such as @(see
vl-follow-scopeexpr)).</li>
<li>@(see vl-elabscopes-item-info) gets the elaboration info for a local item,
if it exists.</li>
</ul>

<p>Except for @(see vl-elabscopes-init), these each take a keyword argument
@(':allow-empty') which determines whether a hard error occurs if the scopes
are empty.</p>")

(define vl-elabscopes-init ()
  :returns (init-scopes vl-elabscopes-p)
  (list (cons nil (make-vl-elabscope))))


(defsection vl-elabscopes-push-scope
  (define vl-scope->elabkey ((scope vl-scope-p))
    :returns (key (and (iff (vl-elabkey-p key) key)
                       (vl-maybe-elabkey-p key)))
    (b* ((name (vl-scope->name scope))
         (type (vl-scope->scopetype scope)))
      (and name
           (case type
             ((:vl-module :vl-interface)
              (vl-elabkey-def name))
             ((:vl-fundecl :vl-taskdecl :vl-genblock :vl-genarrayblock)
              (vl-elabkey-item name))
             (:vl-package (vl-elabkey-package name))
             (otherwise nil)))))

  (define vl-elabscopes-push-anon ((scope vl-elabscope-p)
                                   (scopes vl-elabscopes-p)
                                   &key (allow-empty 'nil))
    (declare (ignore allow-empty))
    :returns (new-scopes vl-elabscopes-p)
    (cons (cons nil (vl-elabscope-fix scope))
          (vl-elabscopes-fix scopes)))
  
  (define vl-elabscopes-push-named ((key vl-elabkey-p)
                                    (scopes vl-elabscopes-p)
                                    &key (allow-empty 'nil))
    :returns (new-scopes vl-elabscopes-p)
    (b* ((scopes (vl-elabscopes-fix scopes))
         ((when (atom scopes))
          (and (not allow-empty)
               (raise "No outer scope -- can't push named scope!"))
          (cons (cons (vl-elabkey-fix key) (make-vl-elabscope)) scopes))
         (curr-elabscope (cdar scopes))
         (new-elabscope (or (vl-elabscope-subscope key curr-elabscope)
                            (make-vl-elabscope))))
      (cons (cons (vl-elabkey-fix key) new-elabscope)
            scopes)))

  (define vl-elabscopes-push-scope ((x vl-scope-p)
                                    (scopes vl-elabscopes-p)
                                    &key (allow-empty 'nil))
    :returns (new-scopes vl-elabscopes-p)
    (b* ((scopes (vl-elabscopes-fix scopes))
         (key (vl-scope->elabkey x))
         ((when key) (vl-elabscopes-push-named key scopes :allow-empty allow-empty)))
      (vl-elabscopes-push-anon (make-vl-elabscope) scopes))))


(define vl-elabscopes-pop ((n natp)
                           (scopes vl-elabscopes-p)
                           &key (allow-empty 'nil))
  :returns (new-scopes vl-elabscopes-p)
  (b* ((scopes (vl-elabscopes-fix scopes)))
  (if (< (lnfix n) (len scopes))
      (nthcdr n scopes)
    (and (not allow-empty)
         (raise "Can't pop ~x0 levels -- only exist ~x1" n (len scopes))))))



(define vl-elabscopes-root ((scopes vl-elabscopes-p)
                            &key (allow-empty 'nil))
  :returns (new-scopes vl-elabscopes-p)
  (b* ((scopes (vl-elabscopes-fix scopes))
       ((when (consp scopes)) (last scopes)))
    (and (not allow-empty)
         (raise "Can't get root scope of empty elabscopes"))))



(defsection vl-elabscopes-traverse

  

  (deftagsum vl-elabinstruction
    :layout :list
    (:pop ((levels natp :rule-classes :type-prescription)))
    (:root ())
    (:push-named ((key vl-elabkey-p)))
    (:push-anon  ((scope vl-elabscope-p))))

  (fty::deflist vl-elabtraversal :elt-type vl-elabinstruction)

  (fty::defalist vl-elabtraversal-stack :key-type vl-elabtraversal :val-type vl-scopestack)

  (define vl-elabscopes-do-instruction ((inst vl-elabinstruction-p)
                                        (scopes vl-elabscopes-p)
                                        &key (allow-empty 'nil))
    :returns (new-scopes vl-elabscopes-p)
    (vl-elabinstruction-case inst
      :pop (vl-elabscopes-pop inst.levels scopes :allow-empty allow-empty)
      :root (vl-elabscopes-root scopes :allow-empty allow-empty)
      :push-anon (vl-elabscopes-push-anon inst.scope scopes :allow-empty allow-empty)
      :push-named (vl-elabscopes-push-named inst.key scopes :allow-empty allow-empty)))

  (define vl-elabscopes-traverse ((trav vl-elabtraversal-p)
                                  (scopes vl-elabscopes-p)
                                  &key (allow-empty 'nil))
    :returns (new-scopes vl-elabscopes-p)
    (if (atom trav)
        (vl-elabscopes-fix scopes)
      (vl-elabscopes-traverse
       (cdr trav)
       (vl-elabscopes-do-instruction (car trav) scopes :allow-empty allow-empty)
       :allow-empty allow-empty))))




(define vl-elabscopes-item-info ((name stringp)
                                 (scopes vl-elabscopes-p)
                                 &key (allow-empty 'nil))
  :returns (info (and (iff (vl-elabinfo-p info) info)
                      (vl-maybe-elabinfo-p info)))
  (b* ((scopes (vl-elabscopes-fix scopes))
       ((when (consp scopes)) (vl-elabscope-item-info name (cdar scopes))))
    (and (not allow-empty)
         (raise "Can't get root scope of empty elabscopes"))))



(define vl-elabscopes-subscope ((key vl-elabkey-p)
                                (scopes vl-elabscopes-p)
                                &key (allow-empty 'nil))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (b* ((scopes (vl-elabscopes-fix scopes))
       ((when (consp scopes)) (vl-elabscope-subscope key (cdar scopes))))
    (and (not allow-empty)
         (raise "Can't get root scope of empty elabscopes"))))

(define vl-elabscopes-update-subscope ((key vl-elabkey-p)
                                       (subscope vl-elabscope-p)
                                       (scopes vl-elabscopes-p)
                                       &key (allow-empty 'nil))
  :returns (new-scopes vl-elabscopes-p)
  (b* ((scopes (vl-elabscopes-fix scopes))
       ((when (consp scopes))
        (cons (cons (caar scopes)
                    (vl-elabscope-update-subscope key subscope (cdar scopes)))
              (cdr scopes))))
    (and (not allow-empty)
         (raise "Can't get root scope of empty elabscopes"))))


(defsection vl-elabscopes-pop/update
  
  (define vl-elabpaths-append ((x vl-elabtraversal-p)
                               (y vl-elabtraversal-p))
    :short "Concatenate two reversed elabtraversals to get a reversed traversal that
          (when followed reversed) to the same place as following @('y') reversed,
          then @('x') reversed."
    :returns (xy vl-elabtraversal-p)
    (cond ((atom x) (vl-elabtraversal-fix y))
          ((vl-elabinstruction-case (car x) :root) (cons (vl-elabinstruction-fix (car x))
                                                         (vl-elabtraversal-fix y)))
          (t (cons (vl-elabinstruction-fix (car x))
                   (vl-elabpaths-append (cdr x) y)))))

  (define vl-elabscopes-pop/update-one ((scopes vl-elabscopes-p))
    :short "Pop a scope off the stack, updating its entry in the outer scope."
    :returns (mv (new-scopes vl-elabscopes-p)
                 (revpath vl-elabtraversal-p))
    (b* ((scopes (vl-elabscopes-fix scopes))
         ((when (< (len scopes) 2))
          (raise "Not enough scopes remaining to pop!~%")
          (mv scopes nil))
         ((list* (cons scope1key scope1) (cons scope2key scope2) rest) scopes)
         ((unless scope1key)
          (mv (cdr scopes) (list (vl-elabinstruction-push-anon scope1))))
         (scope2 (vl-elabscope-update-subscope? scope1key scope1 scope2)))
      (mv (cons (cons scope2key scope2) rest)
          (list (vl-elabinstruction-push-named scope1key))))
    ///
    (local (defthm len-when-consp
             (implies (consp x)
                      (Equal (len x) (+ 1 (len (cdr x)))))))
    ;; (local (defthm len-cdr
    ;;          (equal (len (cdr x))
    ;;                 (max 0 (- (len x) 1)))))

    (defret count-of-vl-elabscopes-pop/update-one-weak
      (<= (len new-scopes)
          (len (vl-elabscopes-fix scopes)))
      :hints (("goal" :cases ((consp (vl-elabscopes-fix scopes))))
              (and stable-under-simplificationp
                   '(:cases ((consp (cdr (vl-elabscopes-fix scopes)))))))
      :rule-classes ((:linear :trigger-terms ((len (mv-nth 0 (vl-elabscopes-pop/update-one scopes)))))))

    (defret count-of-vl-elabscopes-pop/update-one-strong
      (implies (and (consp (vl-elabscopes-fix scopes))
                    (consp (cdr (vl-elabscopes-fix scopes))))
               (< (len new-scopes)
                  (len (vl-elabscopes-fix scopes))))
      :rule-classes ((:linear :trigger-terms ((len (mv-nth 0 (vl-elabscopes-pop/update-one scopes))))))))

  (define vl-elabscopes-pop/update ((n natp)
                                    (scopes vl-elabscopes-p))
    :returns (mv (new-scopes vl-elabscopes-p)
                 (undo vl-elabtraversal-p
                       "First instruction corresponds to the first scope popped.  Therefore,
                        this is a reversed elabpath that reverses this pop
                        operation."))
    :verify-guards nil
    (if (zp n)
        (mv (vl-elabscopes-fix scopes) nil)
      (b* (((mv scopes undo1) (vl-elabscopes-pop/update-one scopes))
           ((mv scopes undo2) (vl-elabscopes-pop/update (1- n) scopes)))
        (mv scopes (vl-elabpaths-append undo1 undo2))))
    ///
    (verify-guards vl-elabscopes-pop/update)))


(define vl-elabscopes-root/update ((scopes vl-elabscopes-p))
  :returns (mv (new-scopes vl-elabscopes-p)
               (undo vl-elabtraversal-p "Reversed elabpath that undoes this traversal"))
  :measure (len (vl-elabscopes-fix scopes))
  :verify-guards nil
  (b* ((scopes (vl-elabscopes-fix scopes))
       ((when (atom scopes))
        (raise "Can't get root scope of empty elabscopes")
        (mv scopes nil))
       ((when (atom (cdr scopes)))
        (mv scopes nil))
       ((mv scopes undo1) (vl-elabscopes-pop/update-one scopes))
       ((mv scopes undo2)
        (vl-elabscopes-root/update scopes)))
    (mv scopes (vl-elabpaths-append undo1 undo2)))
  ///
  (verify-guards vl-elabscopes-root/update))

(defsection vl-elabscopes-traverse/update
  (define vl-elabscopes-do-instruction/update ((inst vl-elabinstruction-p)
                                               (scopes vl-elabscopes-p))
    :returns (mv (new-scopes vl-elabscopes-p)
                 (undo vl-elabtraversal-p "Reversed elabpath that undoes this traversal"))
    (vl-elabinstruction-case inst
      :pop (vl-elabscopes-pop/update inst.levels scopes)
      :root (vl-elabscopes-root/update scopes)
      :push-anon (mv (vl-elabscopes-push-anon inst.scope scopes)
                     (list (vl-elabinstruction-pop 1)))
      :push-named (mv (vl-elabscopes-push-named inst.key scopes)
                      (list (vl-elabinstruction-pop 1)))))

  (define vl-elabscopes-traverse/update ((trav vl-elabtraversal-p)
                                         (scopes vl-elabscopes-p))
    :returns (mv (new-scopes vl-elabscopes-p)
                 (undo vl-elabtraversal-p "Reversed elabpath that undoes this traversal"))
    (if (atom trav)
        (mv (vl-elabscopes-fix scopes) nil)
      (b* (((mv scopes undo1) (vl-elabscopes-do-instruction/update (car trav) scopes))
           ((mv scopes undo2)
            (vl-elabscopes-traverse/update (cdr trav) scopes)))
        (mv scopes (vl-elabpaths-append undo1 undo2))))))




(define vl-elabtraversals-remove-common-prefix ((x vl-elabtraversal-p)
                                                (y vl-elabtraversal-p))
  ;; Takes bottom-up traversals, finds the longest common nil-free prefix, returns
  ;; the bottom-up prefix and suffixes.
  :returns (mv (x-suffix vl-elabtraversal-p)
               (y-suffix vl-elabtraversal-p))
  (if (or (atom x) (atom y)
          (vl-elabinstruction-case (car x) :push-anon)
          (vl-elabinstruction-case (car y) :push-anon)
          (not (vl-elabinstruction-equiv (car x) (car y))))
      (mv (vl-elabtraversal-fix x) (vl-elabtraversal-fix y))
    (vl-elabtraversals-remove-common-prefix (cdr x) (cdr y))))


(define vl-elabscopes->elabtraversal ((x vl-elabscopes-p))
  :short "Returns the reversed traversal necessary to get to the current scope from the top-level design."
  :returns (path vl-elabtraversal-p)
  :measure (len (vl-elabscopes-fix x))
  (b* ((x (vl-elabscopes-fix x)))
    (if (or (atom x)
            (atom (cdr x)))
        nil ;; The design doesn't get an elabkey.
      (cons (if (caar x)
                (vl-elabinstruction-push-named (caar x))
              (vl-elabinstruction-push-anon (cdar x)))
            (vl-elabscopes->elabtraversal (cdr x))))))
       




;; (define vl-scopestack->elabtraversal ((x vl-scopestack-p))
;;   :short "Returns the reversed traversal necessary to get to the scope signified by the current scopestack from the top-level design."
;;   :returns (path vl-elabtraversal-p)
;;   :measure (vl-scopestack-count x)
;;   (vl-scopestack-case x
;;     :null nil
;;     :global nil
;;     :local (cons (let ((key (vl-scope->elabkey x.top)))
;;                    (if key
;;                        (vl-elabinstruction-push-named key)
;;                      (or (raise "Can't create an elabtraversal from scopestack with anonymous scopes")
;;                          (vl-elabinstruction-push-anon (make-vl-elabscope)))))
;;                  (vl-scopestack->elabtraversal x.super))))







;; (define vl-elabscopes-traverse-to-ss ((ss vl-scopestack-p)
;;                                       (scopes vl-elabscopes-p))
;;   :returns (mv (new-scopes vl-elabscopes-p)
;;                (undo vl-elabtraversal-p))
;;   (b* ((curr-path
;;         (rev (vl-elabscopes->elabtraversal scopes)))
;;        (new-path
;;         (rev (vl-scopestack->elabtraversal ss)))
;;        ((mv curr-suffix new-suffix)
;;         (vl-elabtraversals-remove-common-prefix curr-path new-path))
;;        (traversal (cons (vl-elabinstruction-pop (len curr-suffix))
;;                         (rev new-suffix)))
;;        (back-traversal (cons (vl-elabinstruction-pop (len new-suffix))
;;                              (rev curr-suffix))))
;;     (mv (vl-elabscopes-traverse/update traversal scopes)
;;         back-traversal)))




;; (define vl-elabscopes-find-scopecontext ((x vl-scopecontext-p)
;;                                          (scopes vl-elabscopes-p))
;;   :returns (new-scopes vl-elabscopes-p)
;;   :prepwork ((local (defthm vl-elabscope-p-of-car
;;                       (implies (and (vl-elabscopes-p x)
;;                                     (consp x))
;;                                (and (consp (car x))
;;                                     (vl-elabscope-p (cdar x)))))))
;;   (b* ((scopes (vl-elabscopes-fix scopes)))
;;     (vl-scopecontext-case x
;;       :local (if (< x.levels (len scopes))
;;                  (nthcdr x.levels scopes)
;;                (or (raise "Can't go up ~x0 levels -- scopes are ~x1 levels deep" x.levels (len scopes))
;;                    scopes))
;;       :root (if (consp scopes)
;;                 (last scopes)
;;               (raise "Can't go to root context in empty scopes"))
;;       :package (b* (((vl-package x.pkg))
;;                     ((unless (consp scopes))
;;                      (raise "Can't find package ~x0 in empty scopes" x.pkg.name))
;;                     (root-level (last scopes))
;;                     (root (cdar root-level))
;;                     (pkg (vl-elabscope-package-subscope x.pkg.name root)))
;;                  (cons (cons (vl-elabkey-package x.pkg.name)
;;                              (or pkg (make-vl-elabscope))) root-level))
;;       :module (b* (((vl-module x.mod))
;;                    ((unless (consp scopes))
;;                     (raise "Can't find module ~x0 in empty scopes" x.mod.name))
;;                    (root-level (last scopes))
;;                    (root (cdar root-level))
;;                    (mod (vl-elabscope-def-subscope x.mod.name root)))
;;                 (cons (cons (vl-elabkey-def x.mod.name)
;;                             (or mod (make-vl-elabscope))) root-level)))))
                    
      
               

  

;; (define vl-elabscopes-lookup ((name stringp)
;;                               (ss vl-scopestack-p)
;;                               (scopes vl-elabscopes-p))
;;   :returns (info (iff (vl-elabinfo-p info) info))
;;   :prepwork ((local (defthm consp-car-when-elabscopes-p
;;                       (implies (and (vl-elabscopes-p x)
;;                                     (consp x))
;;                                (consp (car x))))))
;;   (b* ((scopes (vl-elabscopes-fix scopes))
;;        (curr-path
;;         (rev (vl-elabscopes->elabtraversal scopes)))
;;        (new-path
;;         (rev (vl-scopestack->elabtraversal ss)))
;;        ((mv curr-suffix new-suffix)
;;         (vl-elabtraversals-remove-common-prefix curr-path new-path))
;;        (lower-scopes (nthcdr (len curr-suffix) scopes))
;;        (ss-scopes (vl-elabscopes-do-traversal new-suffix lower-scopes))
;;        ((unless (consp ss-scopes))
;;         (raise "Empty elabscopes after traversal")))
;;     (vl-elabscope-item-info name (cdar ss-scopes))))







(defstobj elabindex
  (ss :type (satisfies vl-scopestack-p) :initially nil)
  (undostack :type (satisfies vl-elabtraversal-stack-p) :initially nil)
  (scopes :type (satisfies vl-elabscopes-p) :initially nil)
  :renaming ((ss vl-elabindex->ss1)
             (undostack vl-elabindex->undostack1)
             (scopes vl-elabindex->scopes1)
             (update-ss vl-elabindex-update-ss1)
             (update-undostack vl-elabindex-update-undostack1)
             (update-scopes vl-elabindex-update-scopes1)))

(define vl-elabindex->ss (&optional (elabindex 'elabindex))
  :returns (ss vl-scopestack-p)
  (vl-scopestack-fix (vl-elabindex->ss1 elabindex)))

(define vl-elabindex->scopes (&optional (elabindex 'elabindex))
  :returns (scopes vl-elabscopes-p)
  (vl-elabscopes-fix (vl-elabindex->scopes1 elabindex)))

(define vl-elabindex->undostack (&optional (elabindex 'elabindex))
  :returns (undostack vl-elabtraversal-stack-p)
  (vl-elabtraversal-stack-fix (vl-elabindex->undostack1 elabindex)))

(define vl-elabindex-update-ss ((ss vl-scopestack-p)
                                &optional (elabindex 'elabindex))
  (vl-elabindex-update-ss1 (vl-scopestack-fix ss) elabindex))

(define vl-elabindex-update-scopes ((scopes vl-elabscopes-p)
                                &optional (elabindex 'elabindex))
  (vl-elabindex-update-scopes1 (vl-elabscopes-fix scopes) elabindex))

(define vl-elabindex-update-undostack ((undostack vl-elabtraversal-stack-p)
                                       &optional (elabindex 'elabindex))
  (vl-elabindex-update-undostack1 (vl-elabtraversal-stack-fix undostack) elabindex))

(local (in-theory (disable elabindexp)))

(make-event
 (std::da-make-binder 'vl-elabindex '(ss scopes)))

(local (in-theory (disable nth nth-when-zp acl2::nth-when-zp)))

(local (defthm car-when-vl-elabscopes-p
         (implies (and (vl-elabscopes-p x)
                       (consp x))
                  (and (consp (car x))
                       (vl-maybe-elabkey-p (caar x))
                       (vl-elabscope-p (cdar x))))))

(local (defthm car-when-vl-elabtraversal-stack-p
         (implies (and (vl-elabtraversal-stack-p x)
                       (consp x))
                  (and (consp (car x))
                       (vl-elabtraversal-p (caar x))
                       (vl-scopestack-p (cdar x))))))





(define vl-elabindex-update-item-info ((name stringp) (val vl-elabinfo-p)
                                       &key (elabindex 'elabindex))
  (b* ((scopes (vl-elabindex->scopes elabindex))
       ((when (atom scopes))
        (raise "No scope -- can't update item info!~%")
        elabindex)
       ((cons (cons scope1key scope1) rest) scopes)
       (scope1 (vl-elabscope-update-item-info name val scope1)))
    (vl-elabindex-update-scopes (cons (cons scope1key scope1) rest) elabindex)))

(define vl-elabindex-init ((x vl-design-p)
                           &key (elabindex 'elabindex))
  (b* ((elabindex (vl-elabindex-update-ss (vl-scopestack-init x) elabindex)))
    (vl-elabindex-update-scopes (list (cons nil (make-vl-elabscope))) elabindex)))



(define vl-elabindex-traverse ((ss vl-scopestack-p)
                               (path vl-elabtraversal-p)
                               &key (elabindex 'elabindex))
  (b* (((mv scopes rev-undo) (vl-elabscopes-traverse/update path (vl-elabindex->scopes elabindex)))
       (elabindex (vl-elabindex-update-scopes scopes elabindex))
       (elabindex (vl-elabindex-update-undostack (cons (cons (rev rev-undo)
                                                             (vl-elabindex->ss elabindex))
                                                       (vl-elabindex->undostack elabindex))
                                                 elabindex)))
    (vl-elabindex-update-ss (vl-scopestack-fix ss) elabindex)))

(define vl-elabindex-undo (&key (elabindex 'elabindex))
  (b* ((undostack (vl-elabindex->undostack elabindex))
       ((unless (consp undostack))
        (raise "Empty undostack")
        elabindex)
       ((cons undo ss) (car undostack))
       ((mv scopes &) (vl-elabscopes-traverse/update undo (vl-elabindex->scopes elabindex)))
       (elabindex (vl-elabindex-update-scopes scopes elabindex))
       (elabindex (vl-elabindex-update-undostack (cdr undostack) elabindex)))
    (vl-elabindex-update-ss ss elabindex)))

(define vl-elabindex-push ((scope vl-scope-p)
                           &key (elabindex 'elabindex))
  
  (b* ((key (vl-scope->elabkey scope))
       (scopes (vl-elabindex->scopes elabindex))
       (scopes (if key
                   (vl-elabscopes-push-named key scopes)
                 (vl-elabscopes-push-anon (make-vl-elabscope) scopes)))
       (ss (vl-elabindex->ss elabindex))
       (elabindex (vl-elabindex-update-scopes scopes elabindex))
       (elabindex (vl-elabindex-update-undostack (cons (cons (list (vl-elabinstruction-pop 1))
                                                             ss)
                                                       (vl-elabindex->undostack elabindex))
                                                 elabindex)))
    (vl-elabindex-update-ss (vl-scopestack-push scope ss) elabindex)))


       




;; (DEFINE
;;        VL-ELABINDEX-TRAVERSE-TO-SS
;;        ((SS VL-SCOPESTACK-P)
;;         &KEY (ELABINDEX 'ELABINDEX))
;;        (B*
;;         (((MV SCOPES UNDO)
;;           (VL-ELABSCOPES-TRAVERSE-TO-SS SS (VL-ELABINDEX->SCOPES ELABINDEX)))
;;          (ELABINDEX (VL-ELABINDEX-UPDATE-SCOPES SCOPES ELABINDEX))
;;          (ELABINDEX (VL-ELABINDEX-UPDATE-UNDOSTACK
;;                          (CONS (CONS UNDO (VL-ELABINDEX->SS ELABINDEX))
;;                                (VL-ELABINDEX->UNDOSTACK ELABINDEX))
;;                          ELABINDEX)))
;;         (VL-ELABINDEX-UPDATE-SS (VL-SCOPESTACK-FIX SS)
;;                                 ELABINDEX)))
