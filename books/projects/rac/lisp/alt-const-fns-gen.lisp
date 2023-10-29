;; Mayank Manjrekar <mankmonjre@gmail.com>
;; Oct 2023

;; Decomposition of a function is a common technique for reasoning about
;; complex functions. For instance, the correctness of a function can be
;; validated through a sequence of steps that reason about function's local
;; variables. This book implements tools that assist such an approach for
;; functions generated by the rac compiler. In particular, the present tool
;; (ALT-CONS-FNS-GEN) extracts terms that compute values of local variables
;; bound by LET/LET*/MV-LET bindings, which are declared in functions
;; definitions. It takes as input a modification of a function definition,
;; where the user has annotated the variables in LET/LET*/MV-LET bindings. The
;; annotated variables will be extracted as constant functions. A variable is
;; annotated by appending a colon ":" character to it -- for example VAR can be
;; annotated as :VAR, in which case, a constant function named VAR will be
;; generated. To generate a function with a different name, a suffix can be
;; used -- for example, :VAR:VAR-RENAMED to generate function named
;; VAR-RENAMED.
;;
;; Before applying ALT-CONST-FNS-GEN, the user needs to introduce constant
;; functions representind the arguments of the input function. This can be done
;; via an ENCAPSULATE event. For example, suppose an input function has two
;; arguments, we can introduce two constant functions representing these two
;; arguments as follows.

;; (encapsulate
;;   (((a) => *)
;;    ((b) => *))

;;   (local (defun a () <a-value>))
;;   (local (defun b () <b-value>))

;;   (defthm input-constraints-lemma
;;     <constraints-on-the-arguments>))
;;
;; Example application:
;;
;; (defun foo (a b)
;;   (let ((x (+ a b))
;;         (y (* a b)))
;;     (- x y)))
;;
;;  Then, the form
;;  (alt-const-fns-gen
;;    'foo-const
;;    '(defun foo (a b)
;;       (let ((:x (+ a b))
;;             (:y:y-renamed (* a b)))
;;         (- x y))))
;;
;;   generates the following output:
;;   (encapsulate ()
;;     (defundd x () (+ (a) (b)))
;;     (defundd y-renamed () (* a b))
;;     (defundd foo-const () (- (x) (y-renamed)))
;;     (defthmd foo-lemma
;;       (equal (foo-const) (foo (a) (b)))
;;       ...))


;; WARNING: ALT-CONST-FNS-GEN is designed to work on non-recursive functions
;; generated by the RAC parser.

(in-package "ACL2")

(include-book "std/strings/top" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "expand-reduce-cp")

;; ============================================================================

(defmacro defundd (&rest def)
  (declare (xargs :guard (and (true-listp def)
                              (symbolp (car def))
                              (symbol-listp (cadr def)))))
  `(progn
     (defun ,@def)
     (in-theory (disable ,(car def) (,(car def))))))

;; The main structure representing a "processed term". A processed term
;; consists of a main body (inner-most function application) and a context
;; under which it will be evaluated. A list of free-variables is stored in a
;; pterm for computational efficiency.
(fty::defprod pterm
  ((body t)
   (context true-listp)
   (free symbol-listp)))

(define parse-kwd-names ((symb keywordp))
  ;; Return two strings extracted from a keyword.
  ;; E.g. :VAR -> "VAR" "VAR"
  ;; E.g. :VAR:VAR-ALT -> "VAR" "VAR-ALT"
  (b* ((sname (symbol-name symb))
       (names (str::strtok sname '(#\:))))
    (if (and (consp names)
             (not (consp (cdr names))))
        (mv (car names) (car names))
      (if (and (consp names)
               (consp (cdr names))
               (not (consp (cddr names))))
          (mv (car names) (cadr names))
        (b* ((? (raise "Invalid keyword!")))
          (mv "" ""))))))

(program)

(define original-var ((kwd keywordp)
                      (pkg-name stringp))
  ;; Return the original variable corresponding to a renaming expression. If
  ;; the input is not a renaming expression, return the
  (if (keywordp kwd)
      (b* (((mv name ?) (parse-kwd-names kwd)))
        (intern$ name pkg-name))
    kwd))

(define original-vars ((kwds symbol-listp)
                       (pkg-name stringp))
  ;; Process a list of symbols and produce a list of original variables.
  (if (consp kwds)
      (cons (original-var (car kwds) pkg-name) (original-vars (cdr kwds) pkg-name))
    nil))

;; See CONVERT-VAR-IN-TERM for the top-level function, which replaces the
;; variable var with a term var-alt in a term.
(mutual-recursion
 (defun convert-var-in-bindings (var var-alt bindings pkg-name)
   (if (consp bindings)
       (b* (((list lhs rhs) (car bindings)))
         (if (eql (original-var lhs pkg-name) var)
             ;; If lhs is equal to var, then the rest of the bindings/term
             ;; should not be updated. Simply convert the RHS.
             (mv (cons (list lhs (convert-var-in-term var var-alt rhs pkg-name))
                       (cdr bindings))
                 nil)
           ;; Convert the RHS and the rest of the bindings.
           (b* (((mv cdr-bindings cdr-should-convert-body)
                 (convert-var-in-bindings var var-alt (cdr bindings) pkg-name))
                (converted-rhs (convert-var-in-term var var-alt rhs pkg-name)))
             (mv (cons (list lhs converted-rhs) cdr-bindings)
                 cdr-should-convert-body))))
     (mv nil t)))

 (defun convert-var-in-let (var var-alt term pkg-name)
   (b* (((list let-type bindings let-body) term)
         ;; new bindings, and a flag indicating whether the body should be updated
        ((mv bindings should-convert-body)
         (convert-var-in-bindings var var-alt bindings pkg-name)))
     ;; Update let-body only if signaled by the convert-var-in-bindings.
     (list let-type bindings (if should-convert-body (convert-var-in-term var var-alt let-body pkg-name) let-body))))

 (defun convert-var-in-fn-app-args (var var-alt fn-args pkg-name)
   ;; Sequentially update all arguments of a function application.
   (if (consp fn-args)
       (cons (convert-var-in-term var var-alt (car fn-args) pkg-name)
             (convert-var-in-fn-app-args var var-alt (cdr fn-args) pkg-name))
     nil))

 (defun convert-var-in-fn-app (var var-alt term pkg-name)
   ;; Convert a function application
   (b* ((fn-symb (car term))
        (fn-args (cdr term)))
     `(,fn-symb ,@(convert-var-in-fn-app-args var var-alt fn-args pkg-name))))

 (defun convert-var-in-mv-let (var var-alt term pkg-name)
   ;; Convert a mv-let expression
   (b* (((list ? mvl-vars mvl-expr mvl-body) term)
        (mvl-expr (convert-var-in-term var var-alt mvl-expr pkg-name))
        ;; The mvl-body should be updated only if var is not a member of
        ;; mvl-vars.
        (should-convert-body (if (member-equal var (original-vars mvl-vars pkg-name)) nil t))
        (mvl-body (if should-convert-body (convert-var-in-term var var-alt mvl-body pkg-name) mvl-body)))
     `(mv-let ,mvl-vars
        ,mvl-expr
        ,mvl-body)))

 (defun convert-var-in-term (var var-alt term pkg-name)
   ;;; Convert var -> var-alt in term.
   (cond ((and (true-listp term)
               (or (eql (car term) 'let)
                   (eql (car term) 'let*)))
          ;; The term is of the form (LET/LET* BINDINGS LET-BODY)
          (convert-var-in-let var var-alt term pkg-name))
         ((and (true-listp term)
               (eql (car term) 'mv-let))
          ;; The term is of the form (MV-LET MV-VARS MV-EXPR MV-BODY)
          (convert-var-in-mv-let var var-alt term pkg-name))
         ((and (true-listp term) term) ;; non-nil term
          ;; The term is a function application
          (convert-var-in-fn-app var var-alt term pkg-name))
         ((and (symbolp term)
               (eql var term))
          var-alt)
         ;; Default case
         (t term)))
 )

(defun convert-vars-in-term (vars-alist fn-body pkg-name)
  ;;; Sequentially apply transformations in term suggested by var-alist
  (if (consp vars-alist)
      (b* (((cons var var-alt) (car vars-alist)))
        (convert-vars-in-term (cdr vars-alist)
                              (convert-var-in-term var var-alt fn-body pkg-name) pkg-name))
    fn-body))

(defun union-free-vars-of-pterms (pterms)
  ;;; Return a union of free variables of a list of PTERMS
  (if (consp pterms)
      (union$ (pterm->free (car pterms))
              (union-free-vars-of-pterms (cdr pterms)))
    nil))

(defun indexes-of (lst1 lst2)
  ;;; Return indexes of elements of lst1 in lst2
  (if (consp lst1)
      (cons (index-of (car lst1) lst2) (indexes-of (cdr lst1) lst2))
    nil))

;; See add-binding for "main" function of this block.
(mutual-recursion
 (defun simplify-cvar-pterm-of-case-expr (fst len lst pkg-name)
   ;;; Simplify the terms of a case-expression.
   (if (consp lst)
       (b* (((pterm first) (car lst))
            ((list pat val-pterm) first.body)
            (val-pterm (simplify-cvar-pterm fst len val-pterm pkg-name))
            (body `(,pat ,val-pterm))
            (free-vars (pterm->free val-pterm)))
         (cons (pterm body nil free-vars) (simplify-cvar-pterm-of-case-expr fst len (cdr lst) pkg-name)))
     nil))

 (defun simplify-cvar-pterm (cvar-idx len rhs-pterm pkg-name)
   ;;; Create a pterm of the form (MV-NTH IDX (MV-LIST LEN ...)). Simplify if
   ;;; possible.
   (b* (((pterm p) rhs-pterm))
     (cond ((and (true-listp p.body)
                 (eql (car p.body) 'mv))
            ;; (mv-nth n (mv-list len (mv ..))) is just the n-th pterm of mv.
            ;; Take the n-th pterm and add context of rhs-pterm
            (b* ((nth-pterm (nth cvar-idx (cdr p.body))))
              (add-bindings p.context nth-pterm pkg-name)))
           ((and (true-listp p.body)
                 (eql (car p.body) (intern$ "IF1" pkg-name)))
            ;; (mv-nth idx (if1 cond then else)) should be rewritten as
            ;; (if1 cond (mv-nth idx then) (mv-nth idx else))
            (b* (((list ? condition then else) p.body)
                 (then (simplify-cvar-pterm cvar-idx len then pkg-name))
                 (else (simplify-cvar-pterm cvar-idx len else pkg-name))
                 (if1 (intern$ "IF1" pkg-name))
                 (body `(,if1 ,condition ,then ,else))
                 (free-vars (union-free-vars-of-pterms (list condition then else))))
              (pterm body nil free-vars)))
           ((and (true-listp p.body)
                 (eql (car p.body) 'case))
            ;; Similar simplification to the if1 term
            (b* ((lst (cddr p.body))
                 (case-on (cadr p.body))
                 (simplified-lst (simplify-cvar-pterm-of-case-expr cvar-idx len lst pkg-name))
                 (body `(case ,case-on
                          ,@simplified-lst))
                 (free-vars (union-free-vars-of-pterms simplified-lst))
                 (free-vars (union$ (pterm->free case-on) free-vars)))
              (pterm body nil free-vars)))
           (t (b* ((body `(mv-nth ,(pterm cvar-idx nil nil)
                                  ,(pterm `(mv-list ,(pterm len nil nil) ,rhs-pterm) nil p.free))))
                (pterm body nil p.free))))))

 (defun simplify-cvar-pterms (cvar-idxs len rhs-pterm pkg-name)
   ;;; Create multiple pterms with body of the form
   ;;; (mv-nth IDX (MV-LIST LEN ...))
   (if (consp cvar-idxs)
       (cons (simplify-cvar-pterm (car cvar-idxs) len rhs-pterm pkg-name)
             (simplify-cvar-pterms (cdr cvar-idxs) len rhs-pterm pkg-name))
     nil))

 (defun simplify-mv-nth-pterm (common-vars lhs-vars rhs-pterm pkg-name)
   ;;; Simplify a mv-let binding. Ensure the LHS of the mv-let binding only
   ;;; containts common-vars.
   (if (equal (length common-vars) (length lhs-vars))
       `((mv ,@lhs-vars) ,rhs-pterm)
     (b* ((cvar-idxs (indexes-of common-vars lhs-vars))
          ;; Simplified pterms corresponding to common variables.
          (cvar-pterms (simplify-cvar-pterms cvar-idxs (len lhs-vars) rhs-pterm pkg-name)))
       (if (equal (length common-vars) 1)
           (b* (;; Take first and only pterm
                (p (car cvar-pterms))
                ;; add context of the rhs pterm.
                (p (add-bindings (pterm->context rhs-pterm) p pkg-name))
                (var (car common-vars)))
             `(,var ,p))
         (b* (;; Create a pterm with body (mv pterm1 pterm2 ...) for the
              ;; common-vars, with empty context.
              (body `(mv ,@cvar-pterms))
              (free-vars (union-free-vars-of-pterms cvar-pterms))
              (p (pterm body nil free-vars))
              ;; Add context of the RHS.
              (p (add-bindings (pterm->context rhs-pterm) p pkg-name)))
           `((mv ,@common-vars) ,p))))))

;;  (defun add-binding (binding pterm pkg-name)
;; ;;; Add one binding to a pterm. This may update the context of the pterm if
;; ;;; one of the variables in a binding belongs to the free variables of the
;; ;;; pterm -- i.e., evaulating the pterm's body under the require the new
;; ;;; binding in the context. Note: A binding is either of the form (SYMB
;; ;;; PTERM) or ((MV V1 V2 ...) PTERM).
;;    (b* (((pterm x) pterm)
;;         ((list lhs rhs-pterm) binding)
;;         (lhs-vars (if (consp lhs) (cdr lhs) (list lhs)))
;;         (common-vars (intersection$ lhs-vars x.free))
;;         (free-vars (set-difference$ x.free common-vars)))
;;      (if (null common-vars)
;;          ;; no common variable -- the bindings is useless
;;          pterm
;;        (if (equal (length lhs-vars) 1)
;;            ;; Simple let bindings -- add to context and update free-vars
;;            (if (and (symbolp x.body)
;;                     (symbolp lhs)
;;                     (eql x.body lhs))
;;                ;; (let ((x RHS)) x) is just RHS.
;;                rhs-pterm
;;              (b* (;; Update context
;;                   (context (cons binding x.context))
;;                   (rhs-free-vars (pterm->free rhs-pterm))
;;                   ;; Update free variables
;;                   (free-vars (union$ free-vars rhs-free-vars)))
;;                (pterm x.body context free-vars)))
;;          ;; And MV-let binding -- select the common vars and simplify RHS
;;          (b* (;; Simplify (mv-nth n TERM) to reduce number of free variables.
;;               (binding (simplify-mv-nth-pterm common-vars lhs-vars rhs-pterm pkg-name))
;;               ((list lhs rhs-pterm) binding))
;;            (if (and (symbolp x.body)
;;                     (symbolp lhs)
;;                     (eql x.body lhs))
;;                rhs-pterm
;;              (b* (;; Update context
;;                   (context (cons binding x.context))
;;                   ;; Update free-vars
;;                   (free-vars (union$ free-vars (pterm->free (cadr binding)))))
;;                (pterm x.body context free-vars))))))))

 (defun add-binding (binding pterm pkg-name)
;;; Add one binding to a pterm. This may update the context of the pterm if
;;; one of the variables in a binding belongs to the free variables of the
;;; pterm -- i.e., evaulating the pterm's body under the require the new
;;; binding in the context. Note: A binding is either of the form (SYMB
;;; PTERM) or ((MV V1 V2 ...) PTERM).
   (b* (((pterm x) pterm)
        ((list lhs rhs-pterm) binding)
        (lhs-vars (if (consp lhs) (cdr lhs) (list lhs)))
        (common-vars (intersection$ lhs-vars x.free))
        (free-vars (set-difference$ x.free common-vars))
        (binding (if (and (not (null common-vars)) (> (length lhs-vars) 1))
                     (simplify-mv-nth-pterm common-vars lhs-vars rhs-pterm pkg-name)
                   binding))
        ((list lhs rhs-pterm) binding))
     (if (null common-vars)
         ;; no common variable -- the bindings is useless
         pterm
       (if (and (symbolp x.body)
                (symbolp lhs)
                (eql x.body lhs))
           ;; (let ((x RHS)) x) is just RHS.
           rhs-pterm
         (b* (;; Update context
              (context (cons binding x.context))
              (rhs-free-vars (pterm->free rhs-pterm))
              ;; Update free variables
              (free-vars (union$ free-vars rhs-free-vars)))
           (pterm x.body context free-vars))))))


 (defun add-bindings (bindings pterm pkg-name)
   ;;; Add a list of bindings to a pterm. This updates the context of the
   ;;; pterm.
   (if (consp bindings)
       (add-binding (car bindings) (add-bindings (cdr bindings) pterm pkg-name) pkg-name)
     pterm)))

(defun add-binding-to-fns (binding fns pkg-name)
  ;;; Add binding to pterms of a list or (partial) functions.
  (if (consp fns)
      (cons (cons (caar fns) (add-binding binding (cdar fns) pkg-name))
            (add-binding-to-fns binding (cdr fns) pkg-name))
    nil))

(defun add-bindings-to-fns (bindings fns pkg-name)
  ;;; Add a list of bindings to a list of functions.
  (if (consp bindings)
      (add-binding-to-fns (car bindings) (add-bindings-to-fns (cdr bindings) fns pkg-name) pkg-name)
    fns))

(defun kwds-of-list (symb-lst)
  ;;; Subset of keywords in a symbol-list
  (if (consp symb-lst)
      (b* ((cdr-kwd-vars (kwds-of-list (cdr symb-lst))))
        (if (keywordp (car symb-lst))
            (cons (car symb-lst) cdr-kwd-vars)
          cdr-kwd-vars))
    nil))

(defun make-fn (var pterm)
  ;;; (partial) function: a pterm with a variable.
  (cons var pterm))

(defun new-name (kwd pkg-name)
  (if (keywordp kwd)
      (b* (((mv ? name-alt) (parse-kwd-names kwd))
           (name-alt (intern$ name-alt pkg-name)))
        name-alt)
    nil))

(defun new-names (kwds pkg-name)
  (if (consp kwds)
      (cons (new-name (car kwds) pkg-name) (new-names (cdr kwds) pkg-name))
    nil))

(defun zip-names-and-pterms (names pterms)
  ;;; Create functions definitions from a list of names and pterms
  (if (consp names)
      (cons (make-fn (car names) (car pterms))
            (zip-names-and-pterms (cdr names) (cdr pterms)))
    nil))

(defun mv-make-fns (kwd-vars kwd-vars-idx rhs-pterm mvl-len pkg-name)
  ;;; Make functions for mv-let terms for a subset of keywords.
  ;;; Note: the pterm is a simplification of (mv-nth idx rhs-pterm)
  (b* ((pterms (simplify-cvar-pterms kwd-vars-idx mvl-len rhs-pterm pkg-name))
       (names (new-names kwd-vars pkg-name)))
    (zip-names-and-pterms names pterms)))

(define make-args-alist ((args symbol-listp)
                         (pkg-name stringp))
  (if (consp args)
      (if (keywordp (car args))
          (b* (((mv name name-alt) (parse-kwd-names (car args)))
               (var (intern$ name pkg-name))
               (var-alt (intern$ name-alt pkg-name)))
            (cons (cons var `(,var-alt)) (make-args-alist (cdr args) pkg-name)))
        (b* ((var (car args)))
          (cons (cons var `(,var)) (make-args-alist (cdr args) pkg-name))))
    nil))

(defun extract-fns-for-mvl-vars (mvl-vars rhs-pterm mvl-body pkg-name)
  (b* ((kwd-vars (kwds-of-list mvl-vars))
       (kwd-vars-idx (indexes-of kwd-vars mvl-vars))
       (fn-defs (mv-make-fns kwd-vars kwd-vars-idx rhs-pterm (length mvl-vars) pkg-name))
       (var-alist (make-args-alist kwd-vars pkg-name))
       (mvl-body (convert-vars-in-term var-alist mvl-body pkg-name)))
    (mv fn-defs mvl-body)))

(mutual-recursion
 (defun extract-fns-from-bindings (bindings let-body pkg-name)
   ;;; Extract functions from a list of bindings.
   (if (consp bindings)
       (b* ((first-b (car bindings))
            (rest-b (cdr bindings))
            ((list lhs rhs) first-b)
            ((mv rhs-fns rhs-pterm) (extract-fns-from-term rhs pkg-name)))
         (if (not (keywordp lhs))
             ;; Not a keyword: extract fns from the rest of term, and add
             ;; binding to all pterms generated.
             (b* (((mv cdr-fns cdr-pterm) (extract-fns-from-bindings rest-b let-body pkg-name))
                  (cdr-pterm (add-binding `(,lhs ,rhs-pterm) cdr-pterm pkg-name))
                  (cdr-fns (add-binding-to-fns `(,lhs ,rhs-pterm) cdr-fns pkg-name)))
               (mv (append rhs-fns cdr-fns)
                   cdr-pterm))
           ;; In this case, generate fn-def from rhs-pterm, replace variable in
           ;; the rest of the term, and continue extracting functions.
           (b* (((mv name name-alt) (parse-kwd-names lhs))
                (var (intern$ name pkg-name))
                (var-alt (intern$ name-alt pkg-name))
                (fn-def (make-fn var-alt rhs-pterm))
                (var-alt `(,var-alt))
                ((mv rest-b should-convert-body) (convert-var-in-bindings var var-alt rest-b pkg-name))
                (let-body (if should-convert-body (convert-var-in-term var var-alt let-body pkg-name) let-body))
                ((mv cdr-fns cdr-pterm) (extract-fns-from-bindings rest-b let-body pkg-name)))
             (mv (append rhs-fns (list fn-def) cdr-fns)
                 cdr-pterm))))
         ;; Extract functions from the let-body
         (extract-fns-from-term let-body pkg-name)))

 (defun extract-fns-from-let (term pkg-name)
   (b* (((list ?let-type bindings let-body) term))
     (extract-fns-from-bindings bindings let-body pkg-name)))

 (defun extract-fns-from-mv-let (term pkg-name)
   ;;; Generate a list of functions from an mv-let expression
   (b* (((list ? mvl-vars mvl-expr mvl-body) term)
        ;; Get functions from the mvl-expr first
        ((mv rhs-fns rhs-pterm) (extract-fns-from-term mvl-expr pkg-name))
        ;; Create functions for this mv-let binding.
        ;; Note: this modifies the mvl-body
        ((mv mv-fn-defs mvl-body) (extract-fns-for-mvl-vars mvl-vars rhs-pterm mvl-body pkg-name))
        ;; Generate funtions from mvl-body
        (mvl-vars (original-vars mvl-vars pkg-name))
        ((mv cdr-fns cdr-pterm) (extract-fns-from-term mvl-body pkg-name))
        ;; adding the current binding. Note: add-binding will simplify mv-nth
        ;; expression for non-kwd variables.
        (binding `((mv ,@mvl-vars) ,rhs-pterm))
        (cdr-pterm (add-binding binding cdr-pterm pkg-name))
        (cdr-fns (add-binding-to-fns binding cdr-fns pkg-name)))
     (mv (append rhs-fns mv-fn-defs cdr-fns)
         cdr-pterm)))

 (defun extract-fns-from-fn-app-args (fn-args pkg-name)
   ;;; Generate a list of pterms for each arguments of a function.
   (if (consp fn-args)
       (b* (((mv fn-defs p) (extract-fns-from-term (car fn-args) pkg-name))
            ((mv cdr-fn-defs cdr-p) (extract-fns-from-fn-app-args (cdr fn-args) pkg-name)))
         (mv (append fn-defs cdr-fn-defs)
             (cons p cdr-p)))
     (mv nil nil)))

 (defun extract-fns-from-fn-app (term pkg-name)
   ;;; Extract functions from a term which is a function application. The
   ;;; generated pterm's body is of form (fn pterm1 pterm2 ...), which ptermi
   ;;; corresponds to argi of fn.
   (b* ((fn-name (car term))
        (fn-args (cdr term))
        ((mv fn-defs fn-args) (extract-fns-from-fn-app-args fn-args pkg-name))
        (body `(,fn-name ,@fn-args))
        (free-vars (union-free-vars-of-pterms fn-args)))
     (mv fn-defs (pterm body nil free-vars))))

 (defun extract-fns-from-term (term pkg-name)
   ;;; Extract functions from a term. Returns a list of function definitions
   ;;; extracted, and a pterm capturing the residual term, which is equivalent
   ;;; to the original term but in terms of the extracted functions.
   (cond ((and (true-listp term)
               (or (eql (car term) 'let)
                   (eql (car term) 'let*)))
          (extract-fns-from-let term pkg-name))
         ((and (true-listp term)
               (eql (car term) 'mv-let))
          (extract-fns-from-mv-let term pkg-name))
         ((and (true-listp term) term)
          (extract-fns-from-fn-app term pkg-name))
         ((and (symbolp term) term (not (eql term 't)))
          (mv nil (pterm term nil (list term))))
         (t (mv nil (pterm term nil nil))))))

(defun fn-names-of-fns (fns)
  ;;; Function names of fn structure.
  (if (consp fns)
      (cons (caar fns) (fn-names-of-fns (cdr fns)))
    nil))

;; Function to convert a pterm to a normal term.
;; See flattern-pterm for the top-level function
(mutual-recursion
 (defun flatten-context (context)
   (if (consp context)
       (b* (((list lhs rhs-pterm) (car context))
            (rhs (flatten-pterm rhs-pterm)))
         (cons (list lhs rhs) (flatten-context (cdr context))))
     nil))

 (defun flatten-pterms (pterms)
   (if (consp pterms)
       (cons (flatten-pterm (car pterms)) (flatten-pterms (cdr pterms)))
     nil))

 (defun flatten-body (body)
   (if (pterm-p body)
       (flatten-body (pterm->body body))
     (if (and (true-listp body) body)
         `(,(car body) ,@(flatten-pterms (cdr body)))
       body)))

 (defun flatten-pterm (p)
   (if (pterm-p p)
       (b* (((pterm p) p)
            (body (flatten-body p.body)))
         (if p.context
             (b* ((context (flatten-context p.context)))
               `(b* ,context ,body))
           body))
     p)))

(defun flatten-fn (fn)
  ;;; Function to create a function definition from a fn structure.
  (b* (((cons fn-name p) fn)
       ((when (pterm->free p)) (er hard 'flatten-fn "Free variables exist for
~x0: ~x1~%" fn-name (pterm->free p))))
    `(defundd ,fn-name nil
       ,(flatten-pterm p))))

(defun flatten-fns (fns)
  ;;; Create list of fn definitions.
  (if (consp fns)
      (cons (flatten-fn (car fns)) (flatten-fns (cdr fns)))
    nil))

(defun alt-const-fns-gen (fn-name-alt fn-def)
  (b* ((fn-name (cadr fn-def))
       (pkg-name (symbol-package-name fn-name))
       ;; (fn-name-alt (intern$ (concatenate 'string (symbol-name fn-name) "-RESULT") pkg-name))
       (fn-args (caddr fn-def))
       (fn-args-alist (make-args-alist fn-args pkg-name))
       (fn-body (cadddr fn-def))
       (fn-body (convert-vars-in-term fn-args-alist fn-body pkg-name))
       ((mv extracted-fns res-pterm) (extract-fns-from-term fn-body pkg-name))
       (res-fn (make-fn fn-name-alt res-pterm))
       (extracted-fn-names (fn-names-of-fns extracted-fns))
       (theory-list (cons fn-name-alt extracted-fn-names))
       ;; (theory-name (intern$ (concatenate 'string (symbol-name fn-name) "-ALL-FNS") pkg-name))
       (main-lemma-name (intern$ (concatenate 'string (symbol-name fn-name) "-LEMMA") pkg-name)))
    `(encapsulate ()
       (set-ignore-ok t)
       ,@(flatten-fns extracted-fns)
       ,(flatten-fn res-fn)
       ;; (deftheory ,theory-name
       ;;   ',theory-list)
       (defthmd ,main-lemma-name
         (equal (,fn-name-alt)
                ,(convert-vars-in-term fn-args-alist `(,fn-name ,@(original-vars fn-args pkg-name)) pkg-name))
         :hints (("Goal"
                  ;; :do-not '(preprocess)
                  ;; :expand :lambdas
                  ;; :in-theory '(,theory-name ,fn-name)
                  :in-theory nil
                  :clause-processor
                  (expand-reduce-cp clause '(mv-list ,@theory-list ,fn-name) state)))))))
