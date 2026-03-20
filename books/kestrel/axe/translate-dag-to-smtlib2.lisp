; Creating SMT-LIB2 queries from DAGs
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Ensures this book and examples get rebuilt when the script changes:
;; (depends-on "callyices2.bash")

;; This book has a trust tag due to the use of tshell (via call-axe-script).

;; We intentionally reuse the existing STP book for shared DAG/type/counterexample
;; machinery, but emit new SMT-LIB2 syntax and call Yices2.
(include-book "translate-dag-to-stp")
(include-book "kestrel/file-io-light/read-objects-from-file-with-pkg" :dir :system)
(include-book "kestrel/strings-light/parse-decimal-digits" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund smtlib2-call-args (args)
  (declare (xargs :guard t))
  (if (atom args)
      ")"
    (list* " "
           (first args)
           (smtlib2-call-args (rest args)))))

(defund smtlib2-call (op args)
  (declare (xargs :guard (stringp op)))
  (list* "(" op (smtlib2-call-args args)))

(defund smtlib2-let1 (var expr body)
  (declare (xargs :guard t))
  (list* "(let ((" var " " expr ")) " body ")"))

(defund smtlib2-extract (high low expr)
  (declare (xargs :guard (and (natp high)
                              (natp low)
                              (<= low high))))
  (list* "((_ extract "
         (nat-to-string high)
         " "
         (nat-to-string low)
         ") "
         expr
         ")"))

(defund smtlib2-sign-extend (extra-bits expr)
  (declare (xargs :guard (natp extra-bits)))
  (if (zp extra-bits)
      expr
    (list* "((_ sign_extend "
           (nat-to-string extra-bits)
           ") "
           expr
           ")")))

(defund smtlib2-bool-not (arg)
  (smtlib2-call "not" (list arg)))

(defund smtlib2-eq (lhs rhs)
  (smtlib2-call "=" (list lhs rhs)))

(defund smtlib2-ite (test then-branch else-branch)
  (smtlib2-call "ite" (list test then-branch else-branch)))

(defund smtlib2-select (array index)
  (smtlib2-call "select" (list array index)))

(defund smtlib2-store (array index value)
  (smtlib2-call "store" (list array index value)))

(defund smtlib2-space-separate (items)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (if (atom (rest items))
        (list (first items))
      (list* (first items)
             " "
             (smtlib2-space-separate (rest items))))))

(verify-guards smtlib2-call-args)
(verify-guards smtlib2-call)
(verify-guards smtlib2-let1)
(verify-guards smtlib2-extract)
(verify-guards smtlib2-sign-extend)
(verify-guards smtlib2-bool-not)
(verify-guards smtlib2-eq)
(verify-guards smtlib2-ite)
(verify-guards smtlib2-select)
(verify-guards smtlib2-store)
(verify-guards smtlib2-space-separate)

(local
  (defthm string-treep-of-smtlib2-call-args
    (implies (string-treep args)
             (string-treep (smtlib2-call-args args)))
    :hints (("Goal" :in-theory (enable smtlib2-call-args)))))

(local
  (defthm string-treep-of-smtlib2-call
    (implies (and (stringp op)
                  (string-treep args))
             (string-treep (smtlib2-call op args)))
    :hints (("Goal" :in-theory (enable smtlib2-call smtlib2-call-args)))))

(local
  (defthm string-treep-of-smtlib2-let1
    (implies (and (string-treep var)
                  (string-treep expr)
                  (string-treep body))
             (string-treep (smtlib2-let1 var expr body)))
    :hints (("Goal" :in-theory (enable smtlib2-let1)))))

(local
  (defthm string-treep-of-smtlib2-extract
    (implies (string-treep expr)
             (string-treep (smtlib2-extract high low expr)))
    :hints (("Goal" :in-theory (enable smtlib2-extract)))))

(local
  (defthm string-treep-of-smtlib2-sign-extend
    (implies (string-treep expr)
             (string-treep (smtlib2-sign-extend extra-bits expr)))
    :hints (("Goal" :in-theory (enable smtlib2-sign-extend)))))

(local
  (defthm string-treep-of-smtlib2-bool-not
    (implies (string-treep arg)
             (string-treep (smtlib2-bool-not arg)))
    :hints (("Goal" :in-theory (enable smtlib2-bool-not)))))

(local
  (defthm string-treep-of-smtlib2-eq
    (implies (and (string-treep lhs)
                  (string-treep rhs))
             (string-treep (smtlib2-eq lhs rhs)))
    :hints (("Goal" :in-theory (enable smtlib2-eq)))))

(local
  (defthm string-treep-of-smtlib2-ite
    (implies (and (string-treep test)
                  (string-treep then-branch)
                  (string-treep else-branch))
             (string-treep (smtlib2-ite test then-branch else-branch)))
    :hints (("Goal" :in-theory (enable smtlib2-ite)))))

(local
  (defthm string-treep-of-smtlib2-store
    (implies (and (string-treep array)
                  (string-treep index)
                  (string-treep value))
             (string-treep (smtlib2-store array index value)))
    :hints (("Goal" :in-theory (enable smtlib2-store)))))

(local
  (defthm string-treep-of-smtlib2-select
    (implies (and (string-treep array)
                  (string-treep index))
             (string-treep (smtlib2-select array index)))
    :hints (("Goal" :in-theory (enable smtlib2-select smtlib2-call smtlib2-call-args)))))

(local
  (defthm string-treep-of-smtlib2-space-separate
    (implies (string-treep items)
             (string-treep (smtlib2-space-separate items)))
    :hints (("Goal" :in-theory (enable smtlib2-space-separate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-bv-constant-to-smtlib2-aux (val topbit)
  (declare (xargs :guard (and (integerp val)
                              (integerp topbit)
                              (<= -1 topbit))
                  :measure (if (natp topbit) (+ 1 topbit) 0)
                  :split-types t)
           (type integer val))
  (if (not (natp topbit))
      nil
    (cons (if (logbitp topbit val) "1" "0")
          (translate-bv-constant-to-smtlib2-aux val (+ -1 topbit)))))

(local
  (defthm string-treep-of-translate-bv-constant-to-smtlib2-aux
    (string-treep (translate-bv-constant-to-smtlib2-aux val topbit))
    :hints (("Goal" :in-theory (enable translate-bv-constant-to-smtlib2-aux)))))

(defund translate-bv-constant-to-smtlib2 (val size)
  (declare (xargs :guard (and (integerp val)
                              (posp size))
                  :split-types t)
           (type integer val)
           (type (integer 1 *) size))
  (cons "#b" (translate-bv-constant-to-smtlib2-aux val (+ -1 size))))

(defthm string-treep-of-translate-bv-constant-to-smtlib2
  (string-treep (translate-bv-constant-to-smtlib2 val size))
  :hints (("Goal" :in-theory (enable translate-bv-constant-to-smtlib2))))

(defund pad-with-zeros-to-smtlib2 (numzeros bv-string-tree)
  (declare (xargs :guard (and (natp numzeros)
                              (string-treep bv-string-tree))))
  (if (zp numzeros)
      bv-string-tree
    (smtlib2-call "concat"
                  (list (translate-bv-constant-to-smtlib2 0 numzeros)
                        bv-string-tree))))

(local
  (defthm string-treep-of-pad-with-zeros-to-smtlib2
    (implies (string-treep bv-string-tree)
             (string-treep (pad-with-zeros-to-smtlib2 numzeros bv-string-tree)))
    :hints (("Goal" :in-theory (enable pad-with-zeros-to-smtlib2)))))

(defund translate-bvchop-to-smtlib2 (desired-size bv-string-tree)
  (declare (xargs :guard (and (posp desired-size)
                              (string-treep bv-string-tree))))
  (smtlib2-extract (+ -1 desired-size) 0 bv-string-tree))

(local
  (defthm string-treep-of-translate-bvchop-to-smtlib2
    (implies (string-treep bv-string-tree)
             (string-treep (translate-bvchop-to-smtlib2 desired-size bv-string-tree)))
    :hints (("Goal" :in-theory (enable translate-bvchop-to-smtlib2)))))

(defund chop-or-pad-bv-to-smtlib2 (bv-string-tree actual-size desired-size)
  (declare (xargs :guard (and (string-treep bv-string-tree)
                              (posp actual-size)
                              (posp desired-size))))
  (if (< actual-size desired-size)
      (pad-with-zeros-to-smtlib2 (- desired-size actual-size) bv-string-tree)
    (if (> actual-size desired-size)
        (translate-bvchop-to-smtlib2 desired-size bv-string-tree)
      bv-string-tree)))

(local
  (defthm string-treep-of-chop-or-pad-bv-to-smtlib2
    (implies (string-treep bv-string-tree)
             (string-treep (chop-or-pad-bv-to-smtlib2 bv-string-tree actual-size desired-size)))
    :hints (("Goal" :in-theory (enable chop-or-pad-bv-to-smtlib2)))))

(defund translate-boolean-arg-to-smtlib2 (darg dag-array-name dag-array cut-nodenum-type-alist)
  (declare (xargs :guard (and (dargp darg)
                              (boolean-arg-okp darg)
                              (if (consp darg)
                                  t
                                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 darg)))
                              (nodenum-type-alistp cut-nodenum-type-alist))))
  (if (consp darg)
      (if (equal darg *nil*)
          "false"
        (if (equal darg *t*)
            "true"
          (er hard? 'translate-boolean-arg-to-smtlib2 "Bad constant (should be boolean): ~x0.~%" darg)))
    (let ((maybe-type (maybe-get-type-of-nodenum darg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (boolean-typep maybe-type)
          (make-node-var darg)
        (er hard? 'translate-boolean-arg-to-smtlib2 "Bad type, ~x0, for boolean argument ~x1." maybe-type darg)))))

(local
  (defthm string-treep-of-translate-boolean-arg-to-smtlib2
    (string-treep (translate-boolean-arg-to-smtlib2 darg dag-array-name dag-array cut-nodenum-type-alist))
    :hints (("Goal" :in-theory (enable translate-boolean-arg-to-smtlib2)))))

(defund translate-bv-nodenum-and-pad-to-smtlib2 (nodenum desired-size actual-size)
  (declare (xargs :guard (and (natp nodenum)
                              (natp desired-size)
                              (natp actual-size))
                  :split-types t)
           (type (integer 0 *) desired-size actual-size))
  (let ((varname (make-node-var nodenum)))
    (if (< actual-size desired-size)
        (pad-with-zeros-to-smtlib2 (- desired-size actual-size) varname)
      varname)))

(defund translate-bv-arg-and-pad-width-known-to-smtlib2 (arg desired-size actual-size)
  (declare (xargs :guard (and (dargp arg)
                              (bv-arg-okp arg)
                              (posp desired-size)
                              (natp actual-size))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (type (integer 0 *) actual-size))
  (if (consp arg)
      (translate-bv-constant-to-smtlib2 (unquote arg) desired-size)
    (translate-bv-nodenum-and-pad-to-smtlib2 arg desired-size actual-size)))

(defund translate-bv-arg-to-smtlib2 (arg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than arg dag-len)
                              (bv-arg-okp arg)
                              (posp desired-size)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (ignore dag-len))
  (if (consp arg)
      (translate-bv-constant-to-smtlib2 (unquote arg) desired-size)
    (let ((maybe-type (maybe-get-type-of-nodenum arg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (bv-typep maybe-type)
          (translate-bv-nodenum-and-pad-to-smtlib2 arg desired-size (bv-type-width maybe-type))
        (er hard? 'translate-bv-arg-to-smtlib2 "Bad type, ~x0, for BV argument ~x1." maybe-type arg)))))

(defund translate-bv-arg2-to-smtlib2 (darg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than darg dag-len)
                              (bv-arg-okp darg)
                              (posp desired-size)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (ignore dag-len))
  (if (consp darg)
      (translate-bv-constant-to-smtlib2 (unquote darg) desired-size)
    (let ((maybe-type (maybe-get-type-of-nodenum darg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (not (bv-typep maybe-type))
          (er hard? 'translate-bv-arg2-to-smtlib2 "Bad type, ~x0, for BV argument ~x1." maybe-type darg)
        (if (= 0 (bv-type-width maybe-type))
            (er hard? 'translate-bv-arg2-to-smtlib2 "BV of size 0 found: ~x0." darg)
          (chop-or-pad-bv-to-smtlib2 (make-node-var darg)
                                     (bv-type-width maybe-type)
                                     desired-size))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-array-element-equality-to-smtlib2 (lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)
  (declare (xargs :guard (and (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree)
                              (natp lhs-pad-bits)
                              (natp rhs-pad-bits)
                              (posp index-width)
                              (integerp elem-num))))
  (let ((index (translate-bv-constant-to-smtlib2 elem-num index-width)))
    (smtlib2-eq
     (pad-with-zeros-to-smtlib2 lhs-pad-bits
                                (smtlib2-select lhs-string-tree index))
     (pad-with-zeros-to-smtlib2 rhs-pad-bits
                                (smtlib2-select rhs-string-tree index)))))

(local
  (defthm string-treep-of-translate-array-element-equality-to-smtlib2
    (implies (and (string-treep lhs-string-tree)
                  (string-treep rhs-string-tree))
             (string-treep (translate-array-element-equality-to-smtlib2 lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)))
    :hints (("Goal" :in-theory (enable translate-array-element-equality-to-smtlib2)))))

(defund translate-array-equality-to-smtlib2 (n lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width)
  (declare (xargs :guard (and (natp n)
                              (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree)
                              (natp lhs-pad-bits)
                              (natp rhs-pad-bits)
                              (posp index-width))
                  :split-types t)
           (type (integer 0 *) n lhs-pad-bits rhs-pad-bits))
  (if (zp n)
      (translate-array-element-equality-to-smtlib2 lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
    (smtlib2-call "and"
                  (list (translate-array-element-equality-to-smtlib2 lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
                        (translate-array-equality-to-smtlib2 (+ -1 n) lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width)))))

(local
  (defthm string-treep-of-translate-array-equality-to-smtlib2
    (implies (and (string-treep lhs-string-tree)
                  (string-treep rhs-string-tree))
             (string-treep (translate-array-equality-to-smtlib2 n lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width)))
    :hints (("Goal" :in-theory (enable translate-array-equality-to-smtlib2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-equality-of-bvs-to-smtlib2 (lhs rhs lhs-type rhs-type)
  (declare (xargs :guard (and (dargp lhs)
                              (dargp rhs)
                              (bv-typep lhs-type)
                              (bv-typep rhs-type))))
  (let* ((lhs-width (bv-type-width lhs-type))
         (rhs-width (bv-type-width rhs-type)))
    (if (or (zp lhs-width)
            (zp rhs-width))
        (prog2$ (er hard? 'translate-equality-of-bvs-to-smtlib2 "Bit vectors of width 0 are not supported.")
                (mv :bv-of-width-0 nil))
      (let ((max-width (max lhs-width rhs-width)))
        (if (and (bv-arg-okp lhs)
                 (bv-arg-okp rhs))
            (mv (erp-nil)
                (smtlib2-eq
                 (translate-bv-arg-and-pad-width-known-to-smtlib2 lhs max-width lhs-width)
                 (translate-bv-arg-and-pad-width-known-to-smtlib2 rhs max-width rhs-width)))
          (prog2$ (er hard? 'translate-equality-of-bvs-to-smtlib2 "A bad BV arg was found.")
                  (mv :bad-bv-arg nil)))))))

(defund translate-equality-to-smtlib2 (lhs
                                       rhs
                                       dag-array-name dag-array dag-len
                                       cut-nodenum-type-alist constant-array-info)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (or (myquotep lhs)
                                  (and (natp lhs)
                                       (< lhs dag-len)))
                              (or (myquotep rhs)
                                  (and (natp rhs)
                                       (< rhs dag-len)))
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (symbolp dag-array-name)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (disable natp)
                                 :do-not '(generalize eliminate-destructors))))
           (ignore dag-len))
  (let* ((lhs-type (get-type-of-arg-checked lhs dag-array-name dag-array cut-nodenum-type-alist))
         (rhs-type (get-type-of-arg-checked rhs dag-array-name dag-array cut-nodenum-type-alist)))
    (if (and (bv-array-typep lhs-type)
             (bv-array-typep rhs-type)
             (equal (bv-array-type-len lhs-type) (bv-array-type-len rhs-type)))
        (let* ((lhs-element-width (bv-array-type-element-width lhs-type))
               (rhs-element-width (bv-array-type-element-width rhs-type))
               (common-len (bv-array-type-len lhs-type)))
          (if (eql 0 common-len)
              (mv "true" constant-array-info)
            (if (eql 1 common-len)
                (mv (er hard? 'translate-equality-to-smtlib2 "Arrays of length 1 are not supported.")
                    constant-array-info)
              (if (or (zp lhs-element-width)
                      (zp rhs-element-width))
                  (mv (er hard? 'translate-equality-to-smtlib2 "Arrays whose elements have 0 width are not supported.")
                      constant-array-info)
                (mv-let (erp1 lhs-string-tree constant-array-info)
                  (if (atom lhs)
                      (mv nil (make-node-var lhs) constant-array-info)
                    (if (nat-listp (unquote lhs))
                        (mv-let (lhs-string-tree constant-array-info)
                          (translate-constant-array-mention (unquote lhs) lhs-element-width constant-array-info)
                          (mv nil lhs-string-tree constant-array-info))
                      (prog2$ (er hard? 'translate-equality-to-smtlib2 "Bad array constant: ~x0." lhs)
                              (mv t nil constant-array-info))))
                  (mv-let (erp2 rhs-string-tree constant-array-info)
                    (if (atom rhs)
                        (mv nil (make-node-var rhs) constant-array-info)
                      (if (nat-listp (unquote rhs))
                          (mv-let (rhs-string-tree constant-array-info)
                            (translate-constant-array-mention (unquote rhs) rhs-element-width constant-array-info)
                            (mv nil rhs-string-tree constant-array-info))
                        (prog2$ (er hard? 'translate-equality-to-smtlib2 "Bad array constant: ~x0." rhs)
                                (mv t nil constant-array-info))))
                    (if (or erp1 erp2)
                        (mv nil constant-array-info)
                      (mv-let (lhs-pad-bits rhs-pad-bits)
                        (if (<= lhs-element-width rhs-element-width)
                            (mv (nfix (- rhs-element-width lhs-element-width)) 0)
                          (mv 0 (nfix (- lhs-element-width rhs-element-width))))
                        (mv (translate-array-equality-to-smtlib2 (+ -1 common-len)
                                                                 lhs-string-tree
                                                                 rhs-string-tree
                                                                 lhs-pad-bits
                                                                 rhs-pad-bits
                                                                 (ceiling-of-lg common-len))
                            constant-array-info)))))))))
      (if (and (boolean-typep lhs-type)
               (boolean-typep rhs-type))
          (if (and (boolean-arg-okp lhs)
                   (boolean-arg-okp rhs))
              (mv (smtlib2-eq (translate-boolean-arg-to-smtlib2 lhs dag-array-name dag-array cut-nodenum-type-alist)
                              (translate-boolean-arg-to-smtlib2 rhs dag-array-name dag-array cut-nodenum-type-alist))
                  constant-array-info)
            (mv (er hard? 'translate-equality-to-smtlib2 "A bad boolean arg was found.")
                constant-array-info))
        (if (and (bv-typep lhs-type)
                 (bv-typep rhs-type))
            (b* (((mv erp translated-equality)
                  (translate-equality-of-bvs-to-smtlib2 lhs rhs lhs-type rhs-type))
                 ((when erp)
                  (er hard? 'translate-equality-to-smtlib2 "Error translating equality of BVs.")
                  (mv nil constant-array-info)))
              (mv translated-equality constant-array-info))
          (prog2$ (print-array dag-array-name dag-array (max (if (natp lhs) (+ 1 lhs) 0) (if (natp rhs) (+ 1 rhs) 0)))
                  (mv (er hard? 'translate-equality-to-smtlib2 "Trying to equate things of different types (see above for dag): ~x0 (type: ~x1) and ~x2 (type: ~x3).~%"
                          lhs lhs-type rhs rhs-type)
                      constant-array-info)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-smtlib2-array-access-in-bounds (array-name index actual-element-width element-width)
  (declare (xargs :guard (and (string-treep array-name)
                              (string-treep index)
                              (posp actual-element-width)
                              (posp element-width))))
  (let ((array-access (smtlib2-select array-name index)))
    (if (< actual-element-width element-width)
        (pad-with-zeros-to-smtlib2 (- element-width actual-element-width) array-access)
      (if (< element-width actual-element-width)
          (translate-bvchop-to-smtlib2 element-width array-access)
        array-access))))

(defund translate-dag-expr-to-smtlib2 (expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-dag-exprp dag-len expr)
                              (consp expr)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0 dag-exprp natp-of-+-of-1 rationalp-when-integerp)
                                                        (myquotep natp quotep))))))
  (let ((fn (ffn-symb expr)))
    (mv-let (erp translated-expr constant-array-info)
      (case fn
        (quote
         (mv (erp-nil)
             (let ((constant (unquote expr)))
               (if (equal constant t)
                   "true"
                 (if (equal constant nil)
                     "false"
                   (if (natp constant)
                       (translate-bv-constant-to-smtlib2 constant (max 1 (integer-length constant)))
                     (er hard? 'translate-dag-expr-to-smtlib2 "Bad constant: ~x0." constant)))))
             constant-array-info))
        (not
         (if (and (= 1 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr)))
             (mv (erp-nil)
                 (smtlib2-bool-not (translate-boolean-arg-to-smtlib2 (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (booland
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (smtlib2-call "and"
                               (list (translate-boolean-arg-to-smtlib2 (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                                     (translate-boolean-arg-to-smtlib2 (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (boolor
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (smtlib2-call "or"
                               (list (translate-boolean-arg-to-smtlib2 (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                                     (translate-boolean-arg-to-smtlib2 (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (boolif
         (if (and (= 3 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr))
                  (boolean-arg-okp (darg3 expr)))
             (mv (erp-nil)
                 (smtlib2-ite (translate-boolean-arg-to-smtlib2 (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                              (translate-boolean-arg-to-smtlib2 (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                              (translate-boolean-arg-to-smtlib2 (darg3 expr) dag-array-name dag-array cut-nodenum-type-alist))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitnot
         (if (and (= 1 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr)))
             (mv (erp-nil)
                 (smtlib2-call "bvnot"
                               (list (translate-bv-arg2-to-smtlib2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitand
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (smtlib2-call "bvand"
                               (list (translate-bv-arg2-to-smtlib2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                     (translate-bv-arg2-to-smtlib2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitor
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (smtlib2-call "bvor"
                               (list (translate-bv-arg2-to-smtlib2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                     (translate-bv-arg2-to-smtlib2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitxor
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (smtlib2-call "bvxor"
                               (list (translate-bv-arg2-to-smtlib2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                     (translate-bv-arg2-to-smtlib2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bvchop
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvnot
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvnot"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvuminus
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvneg"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (getbit
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((bitnum (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-extract bitnum bitnum
                                    (translate-bv-arg2-to-smtlib2 (darg2 expr) (+ 1 bitnum) dag-array-name dag-array dag-len cut-nodenum-type-alist))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (slice
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-natp (darg1 expr))
                  (darg-quoted-natp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((high (unquote (darg1 expr)))
                   (low (unquote (darg2 expr))))
               (mv (erp-nil)
                   (smtlib2-extract high low
                                    (translate-bv-arg2-to-smtlib2 (darg3 expr) (+ 1 high) dag-array-name dag-array dag-len cut-nodenum-type-alist))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvequal
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-eq (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                               (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvand
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvand"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvor
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvor"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvxor
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvxor"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvplus
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvadd"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvminus
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvsub"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvmult
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvmul"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvdiv
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (unquote (darg1 expr)))
                    (dividend (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (divisor (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (zero (translate-bv-constant-to-smtlib2 0 width)))
               (mv (erp-nil)
                   (smtlib2-ite (smtlib2-eq divisor zero)
                                zero
                                (smtlib2-call "bvudiv" (list dividend divisor)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvmod
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (unquote (darg1 expr)))
                    (dividend (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (divisor (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (zero (translate-bv-constant-to-smtlib2 0 width)))
               (mv (erp-nil)
                   (smtlib2-ite (smtlib2-eq divisor zero)
                                dividend
                                (smtlib2-call "bvurem" (list dividend divisor)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvdiv
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (unquote (darg1 expr)))
                    (dividend (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (divisor (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (zero (translate-bv-constant-to-smtlib2 0 width)))
               (mv (erp-nil)
                   (smtlib2-ite (smtlib2-eq divisor zero)
                                zero
                                (smtlib2-call "bvsdiv" (list dividend divisor)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvrem
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (unquote (darg1 expr)))
                    (dividend (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (divisor (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                    (zero (translate-bv-constant-to-smtlib2 0 width)))
               (mv (erp-nil)
                   (smtlib2-ite (smtlib2-eq divisor zero)
                                dividend
                                (smtlib2-call "bvsrem" (list dividend divisor)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvlt
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvult"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvle
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvule"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvlt
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvslt"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvle
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-call "bvsle"
                                 (list (translate-bv-arg2-to-smtlib2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                       (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvcat
         (if (and (= 4 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (darg-quoted-posp (darg3 expr))
                  (bv-arg-okp (darg4 expr)))
             (mv (erp-nil)
                 (smtlib2-call "concat"
                               (list (translate-bv-arg2-to-smtlib2 (darg2 expr) (unquote (darg1 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                     (translate-bv-arg2-to-smtlib2 (darg4 expr) (unquote (darg3 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bvsx
         (if (and (= 3 (len (dargs expr)))
                  (darg-quoted-integerp (darg1 expr))
                  (darg-quoted-posp (darg2 expr))
                  (<= (unquote (darg2 expr)) (unquote (darg1 expr)))
                  (bv-arg-okp (darg3 expr)))
             (let* ((new-size (unquote (darg1 expr)))
                    (old-size (unquote (darg2 expr))))
               (mv (erp-nil)
                   (smtlib2-sign-extend (- new-size old-size)
                                        (translate-bv-arg2-to-smtlib2 (darg3 expr) old-size dag-array-name dag-array dag-len cut-nodenum-type-alist))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvif
         (if (and (= 4 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (boolean-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr))
                  (bv-arg-okp (darg4 expr)))
             (let ((width (unquote (darg1 expr))))
               (mv (erp-nil)
                   (smtlib2-ite (translate-boolean-arg-to-smtlib2 (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                                (translate-bv-arg2-to-smtlib2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                (translate-bv-arg2-to-smtlib2 (darg4 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (leftrotate32
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let* ((rotate-amount (mod (unquote (darg1 expr)) 32))
                    (translated-arg (translate-bv-arg2-to-smtlib2 (darg2 expr) 32 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
               (mv (erp-nil)
                   (if (= 0 rotate-amount)
                       translated-arg
                     (let ((low-slice-size (- 32 rotate-amount)))
                       (smtlib2-call "concat"
                                     (list (smtlib2-extract (+ -1 low-slice-size) 0 translated-arg)
                                           (smtlib2-extract 31 low-slice-size translated-arg)))))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bv-array-read
         (if (and (= 4 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (darg-quoted-integerp (darg2 expr))
                  (<= 2 (unquote (darg2 expr)))
                  (bv-arg-okp (darg3 expr))
                  (bv-array-arg-okp (unquote (darg2 expr)) (darg4 expr)))
             (b* ((element-width (unquote (darg1 expr)))
                  (len (unquote (darg2 expr)))
                  (index (darg3 expr))
                  (array-arg (darg4 expr))
                  (num-index-bits (ceiling-of-lg len))
                  ((mv array-name constant-array-info actual-element-width)
                   (translate-bv-array-arg array-arg element-width len dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-read
                                           nil
                                           constant-array-info))
                  (trimmed-index (translate-bv-arg2-to-smtlib2 index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist))
                  (access-when-in-bounds (translate-smtlib2-array-access-in-bounds array-name trimmed-index actual-element-width element-width)))
               (mv (erp-nil)
                   (if (power-of-2p len)
                       access-when-in-bounds
                     (smtlib2-ite (smtlib2-call "bvult"
                                                (list trimmed-index
                                                      (translate-bv-constant-to-smtlib2 len num-index-bits)))
                                  access-when-in-bounds
                                  (translate-bv-constant-to-smtlib2 0 element-width)))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bv-array-write
         (if (and (= 5 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (darg-quoted-integerp (darg2 expr))
                  (<= 2 (unquote (darg2 expr)))
                  (bv-arg-okp (darg3 expr))
                  (bv-arg-okp (darg4 expr))
                  (bv-array-arg-okp (unquote (darg2 expr)) (darg5 expr)))
             (b* ((element-width (unquote (darg1 expr)))
                  (len (unquote (darg2 expr)))
                  (index (darg3 expr))
                  (val (darg4 expr))
                  (array-arg (darg5 expr))
                  (num-index-bits (ceiling-of-lg len))
                  ((mv array-name constant-array-info &)
                   (translate-bv-array-arg array-arg element-width len dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-write t constant-array-info))
                  (trimmed-index (translate-bv-arg2-to-smtlib2 index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist))
                  (expr-when-in-bounds
                   (smtlib2-store array-name
                                  trimmed-index
                                  (translate-bv-arg2-to-smtlib2 val element-width dag-array-name dag-array dag-len cut-nodenum-type-alist))))
               (mv (erp-nil)
                   (if (power-of-2p len)
                       expr-when-in-bounds
                     (smtlib2-ite (smtlib2-call "bvult"
                                                (list trimmed-index
                                                      (translate-bv-constant-to-smtlib2 len num-index-bits)))
                                  expr-when-in-bounds
                                  array-name))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bv-array-if
         (if (and (= 5 (len (dargs expr)))
                  (darg-quoted-posp (darg1 expr))
                  (darg-quoted-integerp (darg2 expr))
                  (<= 2 (unquote (darg2 expr)))
                  (boolean-arg-okp (darg3 expr))
                  (bv-array-arg-okp (unquote (darg2 expr)) (darg4 expr))
                  (bv-array-arg-okp (unquote (darg2 expr)) (darg5 expr)))
             (b* ((element-width (unquote (darg1 expr)))
                  (length (unquote (darg2 expr)))
                  (test (darg3 expr))
                  (then-branch (darg4 expr))
                  (else-branch (darg5 expr))
                  ((mv then-array-name constant-array-info &)
                   (translate-bv-array-arg then-branch element-width length dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-if t constant-array-info))
                  ((mv else-array-name constant-array-info &)
                   (translate-bv-array-arg else-branch element-width length dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-if t constant-array-info)))
               (mv (erp-nil)
                   (smtlib2-ite (translate-boolean-arg-to-smtlib2 test dag-array-name dag-array cut-nodenum-type-alist)
                                then-array-name
                                else-array-name)
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (unsigned-byte-p
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (b* ((claimed-width (unquote (darg1 expr)))
                  (bv-arg (darg2 expr))
                  (bv-arg-type (get-type-of-arg-checked bv-arg dag-array-name dag-array cut-nodenum-type-alist))
                  ((when (not (bv-typep bv-arg-type)))
                   (er hard? 'translate-dag-expr-to-smtlib2 "unsigned-byte-p claim applied to non-bv ~x0." bv-arg)
                   (mv (erp-t) nil constant-array-info))
                  (known-width (bv-type-width bv-arg-type))
                  ((when (= 0 known-width))
                   (er hard? 'translate-dag-expr-to-smtlib2 "unsigned-byte-p claim with a width of 0 applied to ~x0." bv-arg)
                   (mv :bad-width nil constant-array-info)))
               (mv (erp-nil)
                   (if (<= known-width claimed-width)
                       "true"
                     (smtlib2-eq
                      (smtlib2-extract (+ -1 known-width) claimed-width
                                       (translate-bv-arg-to-smtlib2 bv-arg known-width dag-array-name dag-array dag-len cut-nodenum-type-alist))
                      (translate-bv-constant-to-smtlib2 0 (- known-width claimed-width))))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (equal
         (if (= 2 (len (dargs expr)))
             (mv-let (translated-expr constant-array-info)
               (translate-equality-to-smtlib2 (darg1 expr)
                                              (darg2 expr)
                                              dag-array-name dag-array dag-len cut-nodenum-type-alist constant-array-info)
               (mv (erp-nil)
                   translated-expr
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (t (mv (erp-t) nil constant-array-info)))
      (if erp
          (prog2$ (er hard? 'translate-dag-expr-to-smtlib2 "Error (~x0) translating expr ~x1.~%" erp expr)
                  (mv nil constant-array-info))
        (mv translated-expr constant-array-info)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-nodes-to-smtlib2 (nodenums-to-translate
                                    dag-array-name
                                    dag-array
                                    dag-len
                                    acc
                                    constant-array-info
                                    cut-nodenum-type-alist)
  (declare (xargs :guard (and (nat-listp nodenums-to-translate)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (string-treep acc)
                              (constant-array-infop constant-array-info)
                              (nodenum-type-alistp cut-nodenum-type-alist))))
  (if (endp nodenums-to-translate)
      (mv acc constant-array-info)
    (let* ((nodenum (first nodenums-to-translate))
           (expr (aref1 dag-array-name dag-array nodenum)))
      (mv-let (translated-expr constant-array-info)
        (translate-dag-expr-to-smtlib2 expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
        (translate-nodes-to-smtlib2 (rest nodenums-to-translate)
                                    dag-array-name
                                    dag-array
                                    dag-len
                                    (smtlib2-let1 (make-node-var nodenum) translated-expr acc)
                                    constant-array-info
                                    cut-nodenum-type-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund smtlib2-type-string (type)
  (declare (xargs :guard (axe-typep type)))
  (if (bv-typep type)
      (list* "(_ BitVec " (nat-to-string (bv-type-width type)) ")")
    (if (bv-array-typep type)
        (let ((len (bv-array-type-len type)))
          (if (< len 2)
              (er hard? 'smtlib2-type-string "Found an array of length 0 or 1 (neither is supported): ~x0." type)
            (list* "(Array (_ BitVec "
                   (nat-to-string (ceiling-of-lg len))
                   ") (_ BitVec "
                   (nat-to-string (bv-array-type-element-width type))
                   "))")))
      (if (boolean-typep type)
          "Bool"
        (if (empty-typep type)
            (er hard? 'smtlib2-type-string "empty type detected.")
          (if (most-general-typep type)
              (er hard? 'smtlib2-type-string "universal type detected.")
            (er hard? 'smtlib2-type-string "Unknown form for type: ~x0." type)))))))

(defund make-smtlib2-type-declarations (nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp nodenum-type-alist)))
  (if (endp nodenum-type-alist)
      nil
    (let* ((entry (first nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry)))
      (list* "(declare-fun "
             (make-node-var nodenum)
             " () "
             (smtlib2-type-string type)
             ")"
             (newline-string)
             (make-smtlib2-type-declarations (rest nodenum-type-alist))))))

(defund make-type-declarations-for-array-constants-to-smtlib2 (constant-array-info)
  (declare (xargs :guard (constant-array-infop constant-array-info)))
  (if (endp constant-array-info)
      nil
    (let* ((entry (first constant-array-info))
           (data (first entry))
           (array-name (second entry))
           (element-width (third entry))
           (index-width (the (integer 1 *) (integer-length (+ -1 (len data))))))
      (list* "(declare-fun "
             array-name
             " () (Array (_ BitVec "
             (nat-to-string index-width)
             ") (_ BitVec "
             (nat-to-string element-width)
             ")))"
             (newline-string)
             (make-type-declarations-for-array-constants-to-smtlib2 (rest constant-array-info))))))

(defund make-value-assertions-for-array-constant-to-smtlib2 (array-data array-name elemnum element-count index-size element-size acc)
  (declare (xargs :guard (and (natp elemnum)
                              (posp index-size)
                              (posp element-size)
                              (natp element-count)
                              (nat-listp array-data)
                              (<= (- element-count elemnum) (len array-data)))
                  :measure (nfix (+ 1 (- element-count elemnum)))))
  (if (or (<= element-count elemnum)
          (not (natp element-count))
          (not (natp elemnum)))
      acc
    (make-value-assertions-for-array-constant-to-smtlib2
     (rest array-data)
     array-name
     (+ 1 elemnum)
     element-count
     index-size
     element-size
     (list* "(assert "
            (smtlib2-eq (smtlib2-select array-name (translate-bv-constant-to-smtlib2 elemnum index-size))
                        (translate-bv-constant-to-smtlib2 (first array-data) element-size))
            ")"
            (newline-string)
            acc))))

(defund make-value-assertions-for-array-constants-to-smtlib2 (constant-array-info acc)
  (declare (xargs :guard (constant-array-infop constant-array-info)))
  (if (endp constant-array-info)
      acc
    (let* ((entry (first constant-array-info))
           (constant-data (first entry))
           (element-count (len constant-data))
           (array-name (second entry))
           (element-width (third entry))
           (index-size (ceiling-of-lg element-count)))
      (if (not (<= 2 element-count))
          (er hard? 'make-value-assertions-for-array-constants-to-smtlib2 "Array is too short: ~x0." entry)
        (make-value-assertions-for-array-constants-to-smtlib2
         (rest constant-array-info)
         (make-value-assertions-for-array-constant-to-smtlib2 constant-data array-name 0 element-count index-size element-width acc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund translate-possibly-negated-nodenum-to-smtlib2 (item)
  (declare (xargs :guard (possibly-negated-nodenump item)))
  (if (consp item)
      (smtlib2-bool-not (make-node-var (farg1 item)))
    (make-node-var item)))

(defund translate-disjunction-to-smtlib2-aux (items)
  (declare (xargs :guard (and (consp items)
                              (possibly-negated-nodenumsp items))))
  (if (endp (rest items))
      (translate-possibly-negated-nodenum-to-smtlib2 (first items))
    (smtlib2-call "or"
                  (list (translate-possibly-negated-nodenum-to-smtlib2 (first items))
                        (translate-disjunction-to-smtlib2-aux (rest items))))))

(defund translate-disjunction-to-smtlib2 (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)))
  (if (endp items)
      "false"
    (translate-disjunction-to-smtlib2-aux items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-counterexample-terms-for-array-to-smtlib2 (nodenum index index-limit index-width acc)
  (declare (xargs :guard (and (natp nodenum)
                              (natp index)
                              (natp index-limit)
                              (<= index index-limit)
                              (posp index-width)
                              (true-listp acc))
                  :measure (nfix (+ 1 (- index-limit index)))))
  (if (or (not (natp index))
          (not (natp index-limit))
          (< index-limit index))
      acc
    (make-counterexample-terms-for-array-to-smtlib2
     nodenum
     (+ 1 index)
     index-limit
     index-width
     (cons (smtlib2-select (make-node-var nodenum)
                           (translate-bv-constant-to-smtlib2 index index-width))
           acc))))

(defund make-counterexample-terms-to-smtlib2 (cut-nodenum-type-alist acc)
  (declare (xargs :guard (and (nodenum-type-alistp cut-nodenum-type-alist)
                              (true-listp acc))))
  (if (endp cut-nodenum-type-alist)
      (reverse-list acc)
    (let* ((entry (first cut-nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry)))
      (make-counterexample-terms-to-smtlib2
       (rest cut-nodenum-type-alist)
       (if (or (boolean-typep type)
               (bv-typep type))
           (cons (make-node-var nodenum) acc)
         (if (bv-array-typep type)
             (let ((len (bv-array-type-len type)))
               (make-counterexample-terms-for-array-to-smtlib2 nodenum
                                                               0
                                                               (+ -1 len)
                                                               (ceiling-of-lg len)
                                                               acc))
           acc))))))

(defund make-get-value-command-to-smtlib2 (cut-nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp cut-nodenum-type-alist)))
  (let ((terms (make-counterexample-terms-to-smtlib2 cut-nodenum-type-alist nil)))
    (if (endp terms)
        nil
      (list* "(get-value ("
             (smtlib2-space-separate terms)
             "))"
             (newline-string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund write-smtlib2-query-to-file (translated-query-core
                                     dag-array-name
                                     dag-array
                                     dag-len
                                     nodenums-to-translate
                                     extra-asserts
                                     filename
                                     cut-nodenum-type-alist
                                     constant-array-info
                                     counterexamplep
                                     print
                                     state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep translated-query-core)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp nodenums-to-translate)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (string-treep extra-asserts)
                              (stringp filename)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (constant-array-infop constant-array-info)
                              (booleanp counterexamplep)
                              (print-levelp print))))
  (prog2$
   (and (print-level-at-least-tp print) (cw "  ~s0~%" filename))
   (mv-let (translation constant-array-info)
     (translate-nodes-to-smtlib2 nodenums-to-translate
                                 dag-array-name
                                 dag-array
                                 dag-len
                                 translated-query-core
                                 constant-array-info
                                 cut-nodenum-type-alist)
     (write-string-tree!
      (list* (if counterexamplep
                 (list "(set-option :produce-models true)" (newline-string))
               nil)
             "(set-logic QF_ABV)" (newline-string)
             (make-smtlib2-type-declarations cut-nodenum-type-alist)
             (make-type-declarations-for-array-constants-to-smtlib2 constant-array-info)
             (make-value-assertions-for-array-constants-to-smtlib2 constant-array-info nil)
             extra-asserts
             "(assert "
             (smtlib2-bool-not translation)
             ")" (newline-string)
             "(check-sat)" (newline-string)
             (if counterexamplep
                 (make-get-value-command-to-smtlib2 cut-nodenum-type-alist)
               nil))
      filename
      'write-smtlib2-query-to-file
      state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund maybe-node-symbol-to-nodenum (sym)
  (declare (xargs :guard t))
  (if (not (symbolp sym))
      nil
    (let ((name (symbol-name sym)))
      (if (or (< (length name) 5)
              (not (equal "NODE" (subseq name 0 4))))
          nil
        (parse-string-as-decimal-number (subseq name 4 (length name)))))))

(defund smtlib2-boolean-valuep (value)
  (declare (xargs :guard t))
  (and (symbolp value)
       (or (equal "TRUE" (symbol-name value))
           (equal "FALSE" (symbol-name value)))))

(defund smtlib2-value-to-acl2 (value)
  (declare (xargs :guard t))
  (if (smtlib2-boolean-valuep value)
      (equal "TRUE" (symbol-name value))
    value))

(defund parse-smtlib2-counterexample-entry (entry)
  (declare (xargs :guard t))
  (if (or (not (true-listp entry))
          (not (= 2 (len entry))))
      :error
    (let ((key (first entry))
          (value (second entry)))
      (if (or (natp value)
              (smtlib2-boolean-valuep value))
          (let ((nodenum (maybe-node-symbol-to-nodenum key)))
            (if nodenum
                (cons nodenum (smtlib2-value-to-acl2 value))
              (if (and (true-listp key)
                       (= 3 (len key))
                       (symbolp (first key))
                       (equal "SELECT" (symbol-name (first key))))
                  (let ((array-nodenum (maybe-node-symbol-to-nodenum (second key)))
                        (index (third key)))
                    (if (and array-nodenum
                             (natp index))
                        (cons (cons array-nodenum index)
                              (smtlib2-value-to-acl2 value))
                      :error))
                :error)))
        :error))))

(defund parse-smtlib2-counterexample-object (entries acc)
  (declare (xargs :guard t))
  (if (endp entries)
      (reverse-list acc)
    (let ((parsed-entry (parse-smtlib2-counterexample-entry (first entries))))
      (if (eq :error parsed-entry)
          :error
        (parse-smtlib2-counterexample-object (rest entries)
                                             (cons parsed-entry acc))))))

(defund parse-yices2-output-objects (objects counterexamplep)
  (declare (xargs :guard (booleanp counterexamplep)))
  (if (endp objects)
      *error*
    (let* ((status (first objects))
           (status-name (and (symbolp status) (symbol-name status))))
      (cond ((equal status-name "UNSAT")
             *valid*)
            ((equal status-name "UNKNOWN")
             *timedout*)
            ((equal status-name "SAT")
             (if counterexamplep
                 (let ((value-object (second objects)))
                   (if (not value-object)
                       *error*
                     (let ((raw-counterexample (parse-smtlib2-counterexample-object value-object nil)))
                       (if (eq :error raw-counterexample)
                           *error*
                         `(,*counterexample* ,raw-counterexample)))))
               *invalid*))
            (t *error*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund call-yices2-on-file (input-filename
                             output-filename
                             print
                             timeout-secs
                             counterexamplep
                             state)
  (declare (xargs :guard (and (stringp input-filename)
                              (stringp output-filename)
                              (print-levelp print)
                              (or (null timeout-secs)
                                  (natp timeout-secs))
                              (booleanp counterexamplep))
                  :stobjs state))
  (b* ((timeout-string (if timeout-secs (nat-to-string timeout-secs) "-1"))
       ((mv start-real-time state) (get-real-time state))
       ((mv status state) (call-axe-script "callyices2.bash" (list input-filename output-filename timeout-string) state))
       ((mv elapsed-time state) (real-time-since start-real-time state)))
    (if (not (eql 0 status))
        (if (eql 201 status)
            (progn$ (er hard? 'call-yices2-on-file "!! ERROR: Unable to find yices-smt2 (define a YICES2 environment var or add its location to your path) !!")
                    (mv *error* state))
          (progn$ (er hard? 'call-yices2-on-file "!! ERROR: Yices2 experienced an unknown error.  Exit status ~x0.  Input:~%~s1~%Output:~%~s2~% !!"
                      status input-filename output-filename)
                  (mv *error* state)))
      (mv-let (erp objects state)
        (read-objects-from-file-with-pkg output-filename "ACL2" state)
        (if erp
            (prog2$ (er hard? 'call-yices2-on-file "Unable to read Yices2 output from file ~x0." output-filename)
                    (mv *error* state))
          (let ((parsed-result (parse-yices2-output-objects objects counterexamplep)))
            (if (eq *error* parsed-result)
                (prog2$ (er hard? 'call-yices2-on-file "Yices2 returned an unexpected result (~x0).  Check the .out file: ~x1.~%" objects output-filename)
                        (mv *error* state))
              (prog2$ (and (print-level-at-least-tp print)
                           (if (eq *valid* parsed-result)
                               (progn$ (cw "  Yices2 said unsat in ")
                                       (print-to-hundredths elapsed-time)
                                       (cw "s.~%"))
                             (if (eq *invalid* parsed-result)
                                 (progn$ (cw "  Yices2 said sat in ")
                                         (print-to-hundredths elapsed-time)
                                         (cw "s.~%"))
                               (if (eq *timedout* parsed-result)
                                   (progn$ (cw "  Yices2 said unknown in ")
                                           (print-to-hundredths elapsed-time)
                                           (cw "s.~%"))
                                 nil))))
                      (mv parsed-result state)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund prove-query-with-yices2 (translated-query-core
                                 extra-string
                                 dag-array-name
                                 dag-array
                                 dag-len
                                 nodenums-to-translate
                                 extra-asserts
                                 base-filename
                                 cut-nodenum-type-alist
                                 print
                                 timeout-secs
                                 constant-array-info
                                 counterexamplep
                                 print-cex-as-signedp
                                 state)
  (declare (xargs :guard (and (nat-listp nodenums-to-translate)
                              (stringp extra-string)
                              (string-treep extra-asserts)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null timeout-secs)
                                  (natp timeout-secs))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (all-< (strip-cars cut-nodenum-type-alist) (alen1 dag-array-name dag-array))
                              (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                              (string-treep translated-query-core)
                              (constant-array-infop constant-array-info))
                  :stobjs state))
  (b* (((mv temp-dir-name state) (maybe-make-temp-dir state))
       (base-filename (concatenate 'string temp-dir-name "/" base-filename))
       (base-filename (maybe-shorten-filename base-filename))
       (- (and (print-level-at-least-tp print) (cw "(Calling Yices2 ~s0 (timeout-secs ~x1):~%" extra-string timeout-secs)))
       (smtlib2-input-filename (string-append base-filename ".smt2"))
       (solver-output-filename (string-append base-filename ".out"))
       ((mv erp state)
        (write-smtlib2-query-to-file translated-query-core
                                     dag-array-name dag-array dag-len
                                     nodenums-to-translate
                                     extra-asserts
                                     smtlib2-input-filename
                                     cut-nodenum-type-alist
                                     constant-array-info
                                     counterexamplep
                                     print
                                     state))
       ((when erp)
        (er hard? 'prove-query-with-yices2 "Unable to write the SMT-LIB2 input file: ~s0 before calling Yices2." smtlib2-input-filename)
        (mv *error* state))
       ((mv erp state)
        (write-strings-to-file! nil solver-output-filename 'prove-query-with-yices2 state))
       ((when erp)
        (er hard? 'prove-query-with-yices2 "Unable to clear the output file: ~s0 before calling Yices2." solver-output-filename)
        (mv *error* state))
       ((mv result state)
        (call-yices2-on-file smtlib2-input-filename solver-output-filename print timeout-secs counterexamplep state))
       (raw-counterexamplep (and (consp result)
                                 (eq *counterexample* (car result))))
       ((mv erp counterexample)
        (if (not raw-counterexamplep)
            (mv (erp-nil) nil)
          (fixup-counterexample (sort-nodenum-type-alist cut-nodenum-type-alist)
                                (cadr result)
                                nil)))
       ((when erp) (mv *error* state))
       (counterexample-certainp (and raw-counterexamplep
                                     (all-cuts-are-at-varsp cut-nodenum-type-alist dag-array-name dag-array)))
       (- (and raw-counterexamplep
               (if counterexample-certainp
                   (cw "Counterexample is certain.~%")
                 (cw "Counterexample is possible (may be spurious).~%"))))
       (result (if raw-counterexamplep
                   (if counterexample-certainp
                       `(,*counterexample* ,counterexample)
                     `(,*possible-counterexample* ,counterexample))
                 result))
       (- (and print
               raw-counterexamplep
               (b* ((- (cw "(Counterexample:~%"))
                    (- (print-counterexample counterexample cut-nodenum-type-alist print-cex-as-signedp dag-array-name dag-array))
                    (- (cw ")~%")))
                 nil)))
       (- (and (print-level-at-least-tp print) (cw "Done calling Yices2.)~%"))))
    (mv result state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund prove-equality-with-yices2 (lhs
                                    rhs
                                    dag-array-name dag-array dag-len
                                    nodenums-to-translate
                                    base-filename
                                    cut-nodenum-type-alist
                                    extra-asserts
                                    print
                                    timeout-secs
                                    counterexamplep
                                    print-cex-as-signedp
                                    state)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (or (myquotep lhs)
                                  (and (natp lhs)
                                       (< lhs dag-len)))
                              (or (myquotep rhs)
                                  (and (natp rhs)
                                       (< rhs dag-len)))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (stringp base-filename)
                              (symbolp dag-array-name)
                              (nat-listp nodenums-to-translate)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (or (null timeout-secs)
                                  (natp timeout-secs))
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                              (string-treep extra-asserts)
                              (print-levelp print))
                  :stobjs state))
  (mv-let (translated-expr constant-array-info)
    (translate-equality-to-smtlib2 lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)
    (prove-query-with-yices2 translated-expr
                             ""
                             dag-array-name
                             dag-array
                             dag-len
                             nodenums-to-translate
                             extra-asserts
                             base-filename
                             cut-nodenum-type-alist
                             print
                             timeout-secs
                             constant-array-info
                             counterexamplep
                             print-cex-as-signedp
                             state)))

(set-verify-guards-eagerness 2)
