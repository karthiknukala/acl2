; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../execution")

(include-book "syntaxp")
(include-book "arrays")
(include-book "convert-integer-value")
(include-book "integer-conversions")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-execution-rules
  :parents (atc-execution)
  :short "Execution rules for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect some rules about the execution of C.
     Some of these rules are used for the symbolic execution
     in the proofs generated by ATC.
     The other rules are used to prove
     the rules used for the symbolic execution.")
   (xdoc::p
    "Some of the rules that are used in the symbolic execution
     rewrite calls of functions used in the deeply embedded dynamic semantics
     into their shallowly embedded counterparts,
     under hypothesis on the types of the arguments.
     For instance, @('(exec-unary op x)')
     is rewritten to @('(<op>-<type> x)')
     when @('op') is @('<op>')
     and @('x') has type @('<type>').
     These shallowly embedded counterparts are used
     in the ACL2 functions from which C code is represented:
     thus, the rewrite rules serve to turn (the execution of) the C code
     into the ACL2 terms from which the C code is generated,
     which is at the core of proving the correctness of the generated C code.")
   (xdoc::p
    "For recursive ACL2 functions that model C execution
     (e.g. @(tsee exec-expr-pure)),
     we introduce opener rules,
     which include @(tsee syntaxp) hypotheses requiring that
     the C abstract syntax being executed is a quoted constant.
     Some of these opener rules include binding hypotheses,
     which avoid symbolically executing the same pieces of C abstract syntax
     multiple times in some situations.")
   (xdoc::p
    "We collect the rules in lists,
     each of which serves a particular symbolic execution purpose.
     Certain rules (proved elsewhere) may appear in multiple lists,
     when they serve multiple symbolic execution purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-const-rules
  :short "Rules for executing constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "To symbolically execute a constant,
     which in our current C subset may only be an integer constant,
     we use rules corresponding to the possible integer types of the constant.
     The rules are openers for @(tsee exec-const),
     under suitable conditions.
     The argument of @(tsee exec-const) is a quoted constant
     during symbolic execution,
     because it is taken from the ASTs being executed;
     thus, we enable the executable counterparts
     of the fixtype functions that operate on constants
     and of the @('<type>-integerp') predicates."))

  (defruled exec-const-to-sint
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (iconst-length-case (iconst->length iconst) :none)
                  (equal value (iconst->value iconst))
                  (sint-integerp value))
             (equal (exec-const const)
                    (sint value)))
    :enable (exec-const
             exec-iconst
             value-sint->get
             sint
             value-kind
             valuep))

  (defruled exec-const-to-slong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (equal value (iconst->value iconst))
                  (slong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst-length-case length :none)
                           (not (sint-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (uint-integerp value))))
                      (iconst-length-case length :long)))
             (equal (exec-const const)
                    (slong value)))
    :enable (exec-const
             exec-iconst
             value-slong->get
             slong
             value-kind
             valuep))

  (defruled exec-const-to-sllong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (equal value (iconst->value iconst))
                  (sllong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst-length-case length :none)
                           (not (slong-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (ulong-integerp value))))
                      (and (iconst-length-case length :long)
                           (not (slong-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (ulong-integerp value))))
                      (iconst-length-case length :llong)))
             (equal (exec-const const)
                    (sllong value)))
    :enable (exec-const
             exec-iconst
             slong-integerp-alt-def
             sint-integerp-alt-def
             ulong-integerp-alt-def
             uint-integerp-alt-def
             value-sllong->get
             sllong
             value-kind
             valuep))

  (defruled exec-const-to-uint
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (iconst-length-case (iconst->length iconst) :none)
                  (equal value (iconst->value iconst))
                  (uint-integerp value)
                  (or (iconst->unsignedp iconst)
                      (and (not (iconst-base-case (iconst->base iconst) :dec))
                           (not (sint-integerp value)))))
             (equal (exec-const const)
                    (uint value)))
    :enable (exec-const
             exec-iconst
             value-uint->get
             uint
             value-kind
             valuep))

  (defruled exec-const-to-ulong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (equal value (iconst->value iconst))
                  (ulong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst->unsignedp iconst)
                           (or (and (iconst-length-case length :none)
                                    (not (uint-integerp value)))
                               (iconst-length-case length :long)))
                      (and (not (iconst-base-case base :dec))
                           (not (slong-integerp value))
                           (or (and (iconst-length-case length :none)
                                    (not (uint-integerp value)))
                               (iconst-length-case length :long)))))
             (equal (exec-const const)
                    (ulong value)))
    :enable (exec-const
             exec-iconst
             sint-integerp-alt-def
             slong-integerp-alt-def
             value-ulong->get
             ulong
             value-kind
             valuep))

  (defruled exec-const-to-ullong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (equal value (iconst->value iconst))
                  (ullong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst->unsignedp iconst)
                           (or (iconst-length-case length :llong)
                               (not (ulong-integerp value))))
                      (and (not (iconst-base-case base :dec))
                           (not (sllong-integerp value))
                           (or (iconst-length-case length :llong)
                               (not (ulong-integerp value))))))
             (equal (exec-const const)
                    (ullong value)))
    :enable (exec-const
             exec-iconst
             sint-integerp-alt-def
             slong-integerp-alt-def
             sllong-integerp-alt-def
             uint-integerp-alt-def
             ulong-integerp-alt-def
             value-ullong->get
             ullong
             value-kind
             valuep))

  (defval *atc-exec-const-rules*
    '(exec-const-to-sint
      exec-const-to-uint
      exec-const-to-slong
      exec-const-to-ulong
      exec-const-to-sllong
      exec-const-to-ullong
      (:e const-kind)
      (:e const-int->get)
      (:e iconst->base)
      (:e iconst->length)
      (:e iconst->unsignedp)
      (:e iconst->value)
      (:e iconst-length-kind)
      (:e iconst-base-kind)
      (:e sint-integerp)
      (:e uint-integerp)
      (:e slong-integerp)
      (:e ulong-integerp)
      (:e sllong-integerp)
      (:e ullong-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-test-rules
  :short "Rules for executing tests on values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each rule turns @('(exec-test x)')
     into @('(boolean-from-<type> x)'),
     where @('<type>') is the type of @('x').
     The @(tsee exec-test) terms result
     from the symbolic execution of the C code,
     while the @('boolean-from-<type>') terms occur
     in the ACL2 functions that represent the C code."))

  (make-event
   `(defruled exec-test-when-scharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (scharp x))
               (equal (exec-test x)
                      (boolean-from-schar x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ucharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ucharp x))
               (equal (exec-test x)
                      (boolean-from-uchar x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sshortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sshortp x))
               (equal (exec-test x)
                      (boolean-from-sshort x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ushortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ushortp x))
               (equal (exec-test x)
                      (boolean-from-ushort x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sintp x))
               (equal (exec-test x)
                      (boolean-from-sint x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-uintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (uintp x))
               (equal (exec-test x)
                      (boolean-from-uint x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-slongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (slongp x))
               (equal (exec-test x)
                      (boolean-from-slong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ulongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ulongp x))
               (equal (exec-test x)
                      (boolean-from-ulong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sllongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sllongp x))
               (equal (exec-test x)
                      (boolean-from-sllong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ullongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ullongp x))
               (equal (exec-test x)
                      (boolean-from-ullong x)))
      :enable exec-test))

  (defval *atc-exec-test-rules*
    '(exec-test-when-scharp
      exec-test-when-ucharp
      exec-test-when-sshortp
      exec-test-when-ushortp
      exec-test-when-sintp
      exec-test-when-uintp
      exec-test-when-slongp
      exec-test-when-ulongp
      exec-test-when-sllongp
      exec-test-when-ullongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-rules
  :short "Rules for @(tsee exec-expr-pure)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('&&') and @('||'),
     we use the auxiliary function @('sint-from-boolean-with-error')
     as an intermediate rewriting stage.")
   (xdoc::p
    "We include the executable counterpart of @(tsee member-equal),
     needed to discharge the hypothesis of
     the rule for strict pure binary expressions.")
   (xdoc::p
    "We include executable counterparts of accessor functions for expressions,
     used to check the kind of expression and to retrieve its constituents."))

  (defruled exec-expr-pure-when-ident
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :ident))
             (equal (exec-expr-pure e compst)
                    (exec-ident (expr-ident->get e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-const
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :const))
             (equal (exec-expr-pure e compst)
                    (exec-const (expr-const->get e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (not (expr-case arr :memberp)))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub (exec-expr-pure arr compst)
                                 (exec-expr-pure (expr-arrsub->sub e) compst)
                                 compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :memberp))
             (equal (exec-expr-pure e compst)
                    (exec-memberp (exec-expr-pure (expr-memberp->target e)
                                                  compst)
                                  (expr-memberp->name e)
                                  compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub-of-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :memberp))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-memberp
                     (exec-expr-pure (expr-memberp->target arr) compst)
                     (expr-memberp->name arr)
                     (exec-expr-pure (expr-arrsub->sub e) compst)
                     compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-unary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :unary)
                  (equal val (exec-expr-pure (expr-unary->arg e) compst))
                  (valuep val))
             (equal (exec-expr-pure e compst)
                    (exec-unary (expr-unary->op e) val)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-cast
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cast))
             (equal (exec-expr-pure e compst)
                    (exec-cast (expr-cast->type e)
                               (exec-expr-pure (expr-cast->arg e) compst))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-strict-pure-binary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (member-equal (binop-kind op)
                                '(:mul :div :rem :add :sub :shl :shr
                                  :lt :gt :le :ge :eq :ne
                                  :bitand :bitxor :bitior)))
             (equal (exec-expr-pure e compst)
                    (exec-binary-strict-pure op
                                             (exec-expr-pure (expr-binary->arg1 e)
                                                             compst)
                                             (exec-expr-pure (expr-binary->arg2 e)
                                                             compst))))
    :enable (exec-expr-pure binop-purep))

  (defund sint-from-boolean-with-error (test)
    (if (errorp test)
        test
      (if test
          (sint 1)
        (sint 0))))

  (defruled exec-expr-pure-when-binary-logand
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logand)
                  (equal test1 (exec-test
                                (exec-expr-pure (expr-binary->arg1 e)
                                                compst)))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (sint-from-boolean-with-error
                         (exec-test
                          (exec-expr-pure (expr-binary->arg2 e) compst)))
                      (sint 0))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-binary-logor
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logor)
                  (equal test1 (exec-test
                                (exec-expr-pure (expr-binary->arg1 e)
                                                compst)))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (sint 1)
                      (sint-from-boolean-with-error
                       (exec-test
                        (exec-expr-pure (expr-binary->arg2 e) compst))))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'test)
                    (booleanp test))
               (equal (sint-from-boolean-with-error test)
                      (if test
                          (sint 1)
                        (sint 0))))
      :enable sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-cond
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cond)
                  (equal test (exec-test
                               (exec-expr-pure (expr-cond->test e) compst)))
                  (booleanp test))
             (equal (exec-expr-pure e compst)
                    (if test
                        (exec-expr-pure (expr-cond->then e) compst)
                      (exec-expr-pure (expr-cond->else e) compst))))
    :enable exec-expr-pure)

  (defval *atc-exec-expr-pure-rules*
    '(exec-expr-pure-when-ident
      exec-expr-pure-when-const
      exec-expr-pure-when-arrsub
      exec-expr-pure-when-memberp
      exec-expr-pure-when-arrsub-of-memberp
      exec-expr-pure-when-unary
      exec-expr-pure-when-cast
      exec-expr-pure-when-strict-pure-binary
      exec-expr-pure-when-binary-logand
      exec-expr-pure-when-binary-logor
      sint-from-boolean-with-error-when-booleanp
      exec-expr-pure-when-cond
      (:e member-equal)
      (:e expr-kind)
      (:e expr-ident->get)
      (:e expr-const->get)
      (:e expr-arrsub->arr)
      (:e expr-arrsub->sub)
      (:e expr-memberp->target)
      (:e expr-memberp->name)
      (:e expr-unary->op)
      (:e expr-unary->arg)
      (:e expr-cast->type)
      (:e expr-cast->arg)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e binop-kind)
      (:e expr-cond->test)
      (:e expr-cond->then)
      (:e expr-cond->else))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-list-rules
  :short "Rules for @(tsee exec-expr-pure-list)."

  (defruled exec-expr-pure-list-of-nil
    (equal (exec-expr-pure-list nil compst)
           nil)
    :enable exec-expr-pure-list)

  (defruled exec-expr-pure-list-when-consp
    (implies (and (syntaxp (quotep es))
                  (consp es)
                  (equal val (exec-expr-pure (car es) compst))
                  (valuep val)
                  (equal vals (exec-expr-pure-list (cdr es) compst))
                  (value-listp vals))
             (equal (exec-expr-pure-list es compst)
                    (cons val vals)))
    :enable exec-expr-pure-list)

  (defval *atc-exec-expr-pure-list-rules*
    '(exec-expr-pure-list-of-nil
      exec-expr-pure-list-when-consp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-call-rules
  :short "Rules for @(tsee exec-expr-call)."

  (defruled exec-expr-call-open
    (implies (and (not (zp limit))
                  (equal vals (exec-expr-pure-list args compst))
                  (value-listp vals))
             (equal (exec-expr-call fun args compst fenv limit)
                    (exec-fun fun vals compst fenv (1- limit))))
    :enable exec-expr-call)

  (defval *atc-exec-expr-call-rules*
    '(exec-expr-call-open)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-call-or-pure-rules
  :short "Rules for @(tsee exec-expr-call-or-pure)."

  (defruled exec-expr-call-or-pure-when-pure
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (zp limit))
                  (compustatep compst))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (mv (exec-expr-pure e compst)
                        compst)))
    :enable exec-expr-call-or-pure)

  (defruled exec-expr-call-of-pure-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit)))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (exec-expr-call (expr-call->fun e)
                                    (expr-call->args e)
                                    compst
                                    fenv
                                    (1- limit))))
    :enable exec-expr-call-or-pure)

  (defval *atc-exec-expr-call-or-pure-rules*
    '(exec-expr-call-or-pure-when-pure
      exec-expr-call-of-pure-when-call
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-call-or-asg-rules
  :short "Rules for @(tsee exec-expr-call-or-asg)."

  (defruled exec-expr-call-or-asg-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit))
                  (equal val?+compst1
                         (exec-expr-call (expr-call->fun e)
                                         (expr-call->args e)
                                         compst
                                         fenv
                                         (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    compst1))
    :enable exec-expr-call-or-asg)

  (defruled exec-expr-call-or-asg-when-asg
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (zp limit))
                  (compustatep compst))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    (exec-expr-asg e compst fenv (1- limit))))
    :enable exec-expr-call-or-asg)

  (defval *atc-exec-expr-call-or-asg-rules*
    '(exec-expr-call-or-asg-when-call
      exec-expr-call-or-asg-when-asg
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-fun-rules
  :short "Rules for @(tsee exec-fun)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proofs generated by ATC are modularized
     so that there is one theorem per non-recursive target function.
     So we generally do not expand calls of @(tsee exec-fun),
     except in the theorem for the function in question.
     We rely on the fact that the correctness theorems
     for the functions called by the function in question
     come after the following rule in the ACL2 history
     (because they are generated by ATC as part of the generated events),
     and thus take precedence over this rule:
     in other words, given theorems for the called functions,
     this rule is expected to apply only on the function in question,
     i.e. the one whose correctness theorem is being proved.
     Note that these theorems are generated only for non-recursive functions;
     the recursive functions represent loops,
     and their correctness theorems do not involve @(tsee exec-fun)."))

  (defruled exec-fun-open
    (implies (and (not (zp limit))
                  (equal info (fun-env-lookup fun fenv))
                  info
                  (equal scope (init-scope (fun-info->params info) args))
                  (scopep scope)
                  (equal val?+compst1
                         (exec-block-item-list (fun-info->body info)
                                               (push-frame (make-frame
                                                            :function fun
                                                            :scopes (list
                                                                     scope))
                                                           compst)
                                    fenv
                                    (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?)
                  (equal (type-of-value-option val?)
                         (tyname-to-type (fun-info->result info))))
             (equal (exec-fun fun args compst fenv limit)
                    (mv val? (pop-frame compst1))))
    :enable exec-fun)

  (defval *atc-exec-fun-rules*
    '(exec-fun-open
      (:e fun-info->params)
      (:e fun-info->result)
      (:e fun-info->body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-stmt-rules
  :short "Rules for @(tsee exec-stmt)."

  (defruled exec-stmt-when-compound
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :compound)
                  (not (zp limit))
                  (equal val?+compst1
                         (exec-block-item-list (stmt-compound->items s)
                                               (enter-scope compst)
                                               fenv
                                               (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?))
             (equal (exec-stmt s compst fenv limit)
                    (mv val? (exit-scope compst1))))
    :enable exec-stmt)

  (defruled exec-stmt-when-expr
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :expr)
                  (not (zp limit))
                  (equal compst1
                         (exec-expr-call-or-asg (stmt-expr->get s)
                                                compst
                                                fenv
                                                (1- limit)))
                  (compustatep compst1))
             (equal (exec-stmt s compst fenv limit)
                    (mv nil compst1)))
    :enable exec-stmt)

  (defruled exec-stmt-when-if
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :if)
                  (not (zp limit))
                  (compustatep compst)
                  (equal test
                         (exec-test (exec-expr-pure (stmt-if->test s) compst)))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt (stmt-if->then s) compst fenv (1- limit))
                      (mv nil compst))))
    :enable exec-stmt)

  (defruled exec-stmt-when-ifelse
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :ifelse)
                  (not (zp limit))
                  (equal test
                         (exec-test
                          (exec-expr-pure (stmt-ifelse->test s) compst)))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt (stmt-ifelse->then s) compst fenv (1- limit))
                      (exec-stmt (stmt-ifelse->else s) compst fenv (1- limit)))))
    :enable exec-stmt)

  (defruled exec-stmt-when-while
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :while)
                  (not (zp limit)))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt-while (stmt-while->test s)
                                     (stmt-while->body s)
                                     compst
                                     fenv
                                     (1- limit))))
    :enable exec-stmt)

  (defruled exec-stmt-when-return
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :return)
                  (not (zp limit))
                  (equal e (stmt-return->value s))
                  e
                  (equal val+compst1
                         (exec-expr-call-or-pure e compst fenv (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-stmt s compst fenv limit)
                    (mv val compst1)))
    :enable exec-stmt)

  (defval *atc-exec-stmt-rules*
    '(exec-stmt-when-compound
      exec-stmt-when-expr
      exec-stmt-when-if
      exec-stmt-when-ifelse
      exec-stmt-when-while
      exec-stmt-when-return
      (:e stmt-kind)
      (:e stmt-compound->items)
      (:e stmt-expr->get)
      (:e stmt-if->test)
      (:e stmt-if->then)
      (:e stmt-ifelse->test)
      (:e stmt-ifelse->then)
      (:e stmt-ifelse->else)
      (:e stmt-while->test)
      (:e stmt-while->body)
      (:e stmt-return->value))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-initer-rules
  :short "Rules for @(tsee exec-initer)."

  (defruled exec-initer-when-single
    (implies (and (syntaxp (quotep initer))
                  (equal (initer-kind initer) :single)
                  (not (zp limit))
                  (equal expr (initer-single->get initer))
                  (equal val+compst1
                         (exec-expr-call-or-pure expr compst fenv (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-initer initer compst fenv limit)
                    (mv (init-value-single val) compst1)))
    :enable exec-initer)

  (defval *atc-exec-initer-rules*
    '(exec-initer-when-single
      (:e initer-kind)
      (:e initer-single->get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-init-value-to-value-rules
  :short "Rules for @(tsee init-value-to-value)."

  (defruled init-value-to-value-when-single
    (implies (and (valuep val)
                  (equal (type-of-value val)
                         type))
             (equal (init-value-to-value type (init-value-single val))
                    val))
    :enable init-value-to-value)

  (defval *atc-init-value-to-value-rules*
    '(init-value-to-value-when-single)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-block-item-rules
  :short "Rules for @(tsee exec-block-item)."

  (defruled exec-block-item-when-declon
    (implies (and (syntaxp (quotep item))
                  (equal (block-item-kind item) :declon)
                  (not (zp limit))
                  (equal declon (block-item-declon->get item))
                  (equal var+tyname+init
                         (obj-declon-to-ident+tyname+init declon))
                  (equal var (mv-nth 0 var+tyname+init))
                  (equal tyname (mv-nth 1 var+tyname+init))
                  (equal init (mv-nth 2 var+tyname+init))
                  init
                  (equal type (tyname-to-type tyname))
                  (not (type-case type :array))
                  (equal ival+compst1
                         (exec-initer init compst fenv (1- limit)))
                  (equal ival (mv-nth 0 ival+compst1))
                  (equal compst1 (mv-nth 1 ival+compst1))
                  (init-valuep ival)
                  (equal val (init-value-to-value type ival))
                  (valuep val)
                  (equal compst2 (create-var var val compst1))
                  (compustatep compst2))
             (equal (exec-block-item item compst fenv limit)
                    (mv nil compst2)))
    :enable exec-block-item)

  (defruled exec-block-item-when-stmt
    (implies (and (syntaxp (quotep item))
                  (equal (block-item-kind item) :stmt)
                  (not (zp limit)))
             (equal (exec-block-item item compst fenv limit)
                    (exec-stmt (block-item-stmt->get item)
                               compst
                               fenv
                               (1- limit))))
    :enable exec-block-item)

  (defval *atc-exec-block-item-rules*
    '(exec-block-item-when-declon
      exec-block-item-when-stmt
      (:e block-item-kind)
      (:e block-item-declon->get)
      (:e block-item-stmt->get)
      (:e obj-declon-to-ident+tyname+init)
      return-type-of-init-value-single)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-block-item-list-rules
  :short "Rules for @(tsee exec-block-item-list)."

  (defruled exec-block-item-list-of-nil
    (implies (and (not (zp limit))
                  (compustatep compst))
             (equal (exec-block-item-list nil compst fenv limit)
                    (mv nil compst)))
    :enable exec-block-item-list)

  (defruled exec-block-item-list-when-consp
    (implies (and (syntaxp (quotep items))
                  (consp items)
                  (not (zp limit))
                  (equal val?+compst1
                         (exec-block-item (car items) compst fenv (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (value-optionp val?)
                  (equal compst1 (mv-nth 1 val?+compst1)))
             (equal (exec-block-item-list items compst fenv limit)
                    (if val?
                        (mv val? compst1)
                      (exec-block-item-list (cdr items)
                                            compst1
                                            fenv
                                            (1- limit)))))
    :enable exec-block-item-list)

  (defval *atc-exec-block-item-list-rules*
    '(exec-block-item-list-of-nil
      exec-block-item-list-when-consp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-init-scope-rules
  :short "Rules for @(tsee init-scope)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The base case is a call @('(init-scope nil nil)'),
     which is handled by the executable counterpart of @(tsee init-scope).
     For the step case, during symbolic execution we expect that
     there is always the same number of formals and actuals.")
   (xdoc::p
    "We need to enable @(tsee eq) because it arises from
     the translation of @('(obj-declor-case declor :pointer)')
     in one of the hypotheses of the rule."))

  (defruled init-scope-when-consp
    (implies (and (syntaxp (quotep formals))
                  (consp formals)
                  (equal formal (car formals))
                  (param-declonp formal)
                  (valuep val)
                  (equal name+tyname (param-declon-to-ident+tyname formal))
                  (equal name (mv-nth 0 name+tyname))
                  (equal tyname (mv-nth 1 name+tyname))
                  (equal (type-of-value val)
                         (tyname-to-type tyname))
                  (value-listp vals)
                  (equal scope (init-scope (cdr formals) vals))
                  (scopep scope)
                  (not (omap::in name scope)))
             (equal (init-scope formals (cons val vals))
                    (omap::update name val scope)))
    :enable init-scope)

  (defval *atc-init-scope-rules*
    '(init-scope-when-consp
      eq
      (:e init-scope)
      (:e param-declonp)
      (:e param-declon-to-ident+tyname))))
