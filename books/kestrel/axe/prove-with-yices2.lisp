; Calling Yices2 to prove things about DAGs and terms
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prove-with-stp")
(include-book "prove-with-stp2")
(include-book "translate-dag-to-smtlib2")
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(set-verify-guards-eagerness 0)

(defconst *default-yices2-timeout-secs* 60)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm rationalp-when-natp
    (implies (natp x)
             (rationalp x))))

(local
  (defthm <=-of-midpoint-and-max-depth
    (implies (and (integerp min-depth)
                  (<= 0 min-depth)
                  (integerp max-depth)
                  (<= 0 max-depth)
                  (<= min-depth max-depth))
             (<= (ceiling (+ (* 1/2 max-depth) (* 1/2 min-depth)) 1)
                 max-depth))
    :hints (("Goal"
             :use ((:instance <-of-ceiling-arg2
                              (i (+ (* 1/2 max-depth) (* 1/2 min-depth)))
                              (j 1)
                              (k (+ 1 max-depth))))
             :in-theory (disable <-of-ceiling-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund prove-disjunction-with-yices2-at-depth (depth-limit
                                                disjuncts
                                                depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                base-filename
                                                print timeout-secs counterexamplep print-cex-as-signedp state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (or (natp depth-limit) (equal nil depth-limit))
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (implies depth-limit (array1p 'depth-array depth-array))
                              (if depth-limit (all-< (strip-nots-from-possibly-negated-nodenums disjuncts) (alen1 'depth-array depth-array)) t)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (all-< (strip-cars known-nodenum-type-alist) dag-len)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state))
  (b* ((handled-node-array (make-empty-array 'handled-node-array (+ 1 (max-nodenum-in-possibly-negated-nodenums disjuncts))))
       ((mv erp disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)
        (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array
                                           dag-array dag-len dag-parent-array
                                           known-nodenum-type-alist
                                           nil
                                           nil
                                           nil))
       ((when erp) (mv :error state))
       ((when (not (consp disjuncts-to-include-in-query)))
        (cw "Note: No disjuncts. Not calling Yices2.~%")
        (mv :invalid state)))
    (prove-query-with-yices2 (translate-disjunction-to-smtlib2 disjuncts-to-include-in-query)
                             (if depth-limit (concatenate 'string "at depth " (nat-to-string depth-limit)) "on uncut goal")
                             'dag-array dag-array dag-len
                             (reverse (merge-sort-< nodenums-to-translate))
                             nil
                             (concatenate 'string base-filename (if depth-limit (concatenate 'string "-depth-" (nat-to-string depth-limit)) "-uncut"))
                             cut-nodenum-type-alist
                             print
                             timeout-secs
                             nil
                             counterexamplep
                             print-cex-as-signedp
                             state)))

(defund prove-disjunction-with-yices2-at-depths (min-depth
                                                 max-depth
                                                 depth-array
                                                 known-nodenum-type-alist
                                                 disjuncts
                                                 dag-array
                                                 dag-len
                                                 dag-parent-array
                                                 base-filename
                                                 print
                                                 timeout-secs
                                                 counterexamplep
                                                 print-cex-as-signedp
                                                 state)
  (declare (xargs :guard (and (posp min-depth)
                              (natp max-depth)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (all-< (strip-cars known-nodenum-type-alist) dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (array1p 'depth-array depth-array)
                              (all-< (strip-nots-from-possibly-negated-nodenums disjuncts)
                                     (alen1 'depth-array depth-array))
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state
                  :measure (nfix (+ 1 (- max-depth min-depth)))))
  (if (or (not (mbt (natp min-depth)))
          (not (natp max-depth))
          (< max-depth min-depth))
      (prog2$ (cw "No more depths to try.~%")
              (mv *timedout* state))
    (b* ((depth min-depth)
         ((mv result state)
          (prove-disjunction-with-yices2-at-depth depth disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                  base-filename print timeout-secs counterexamplep print-cex-as-signedp state)))
      (if (eq result *error*)
          (mv *error* state)
        (if (eq result *valid*)
            (mv *valid* state)
          (if (eq result *timedout*)
              (mv *timedout* state)
            (prove-disjunction-with-yices2-at-depths (+ 1 depth)
                                                     max-depth
                                                     depth-array
                                                     known-nodenum-type-alist
                                                     disjuncts
                                                     dag-array dag-len dag-parent-array
                                                     base-filename print timeout-secs counterexamplep print-cex-as-signedp
                                                     state)))))))

(defund prove-disjunction-with-yices2 (disjuncts
                                       dag-array
                                       dag-len
                                       dag-parent-array
                                       base-filename
                                       print
                                       timeout-secs
                                       counterexamplep
                                       print-cex-as-signedp
                                       state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state))
  (b* ((disjunction (get-axe-disjunction-from-dag-items disjuncts 'dag-array dag-array dag-len))
       ((when (disjunction-is-truep disjunction))
        (prog2$ (cw "(Note: Disjunction is obviously true. Proved it.)~%")
                (mv *valid* state)))
       ((when (disjunction-is-falsep disjunction))
        (prog2$ (cw "(Note: Disjunction is obviously false. Failed to prove it.)~%")
                (mv *invalid* state)))
       (disjuncts disjunction)
       (known-nodenum-type-alist (build-known-nodenum-type-alist disjuncts dag-array dag-len))
       (maybe-node-given-empty-type (node-given-empty-type known-nodenum-type-alist))
       ((when maybe-node-given-empty-type)
        (cw "(WARNING: Goal is true due to type mismatch on:~%")
        (print-dag-array-node-and-supporters 'dag-array dag-array maybe-node-given-empty-type)
        (cw ")~%")
        (mv *valid* state))
       (- (and (print-level-at-least-tp print) (cw "(Calling Yices2 (perhaps at several depths) on ~s0.~%" base-filename)))
       ((mv result state)
        (prove-disjunction-with-yices2-at-depth nil
                                                disjuncts
                                                nil
                                                dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                base-filename print timeout-secs counterexamplep print-cex-as-signedp state)))
    (if (eq result *error*)
        (mv *error* state)
      (if (eq result *valid*)
          (prog2$ (and (print-level-at-least-tp print) (cw "Yices2 proved the uncut goal ~s0.)~%" base-filename))
                  (mv *valid* state))
        (if (eq result *invalid*)
            (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename))
                    (mv *invalid* state))
          (if (call-of *counterexample* result)
              (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename))
                      (mv result state))
            (if (call-of *possible-counterexample* result)
                (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename))
                        (mv result state))
              (if (eq result *timedout*)
                  (b* (((mv depth-array max-depth)
                        (make-depth-array-for-nodes (strip-nots-from-possibly-negated-nodenums disjuncts)
                                                    'dag-array dag-array dag-len))
                       ((mv result state)
                        (prove-disjunction-with-yices2-at-depths 1
                                                                 max-depth
                                                                 depth-array
                                                                 known-nodenum-type-alist
                                                                 disjuncts
                                                                 dag-array dag-len dag-parent-array
                                                                 base-filename
                                                                 print timeout-secs counterexamplep print-cex-as-signedp
                                                                 state)))
                    (if (eq result *error*)
                        (mv *error* state)
                      (if (eq result *valid*)
                          (prog2$ (and (print-level-at-least-tp print) (cw "Yices2 proved ~s0.)~%" base-filename))
                                  (mv *valid* state))
                        (if (eq result *invalid*)
                            (prog2$ (and (print-level-at-least-tp print) (cw "Yices2 failed to find a depth at which ~s0 would be valid.)~%" base-filename))
                                    (mv *invalid* state))
                          (prog2$ (and (print-level-at-least-tp print) (cw "Yices2 failed to find a depth at which ~s0 would be valid.)~%" base-filename))
                                  (mv *timedout* state))))))
                (mv (er hard? 'prove-disjunction-with-yices2 "Bad result, ~x0, from prove-disjunction-with-yices2-at-depth." result)
                    state)))))))))

(defund prove-implication-with-yices2 (hyps
                                       conc
                                       dag-array
                                       dag-len
                                       dag-parent-array
                                       base-filename
                                       print
                                       timeout-secs
                                       counterexamplep
                                       print-cex-as-signedp
                                       state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenump conc dag-len)
                              (bounded-possibly-negated-nodenumsp hyps dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state))
  (prove-disjunction-with-yices2 (cons conc (negate-possibly-negated-nodenums hyps))
                                 dag-array dag-len dag-parent-array
                                 base-filename
                                 print timeout-secs counterexamplep print-cex-as-signedp
                                 state))

(defund prove-clause-with-yices2 (clause counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null timeout-secs) (natp timeout-secs))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state))
  (b* (((when (not clause))
        (cw "(Note: Cannot prove the empty clause.)~%")
        (mv *invalid* state))
       ((mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array & &)
        (make-terms-into-dag-array-basic clause 'dag-array 'dag-parent-array nil))
       ((when erp) (mv *error* state))
       ((mv provedp nodenums)
        (handle-constant-disjuncts nodenums-or-quoteps nil)))
    (if provedp
        (prog2$ (cw "(Note: Proved the clause because of a constant disjunct.)~%")
                (mv *valid* state))
      (if (not nodenums)
          (prog2$ (cw "(FAILED: Failed to prove the clause because all disjuncts are nil constants.)~%")
                  (mv *invalid* state))
        (prove-disjunction-with-yices2 nodenums
                                       dag-array
                                       dag-len
                                       dag-parent-array
                                       base-filename
                                       print
                                       timeout-secs
                                       counterexamplep
                                       print-cex-as-signedp
                                       state)))))

(defund prove-term-implication-with-yices2 (conc hyps counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null timeout-secs) (natp timeout-secs))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state))
  (let ((clause (cons conc (wrap-all 'not hyps))))
    (prove-clause-with-yices2 clause counterexamplep print-cex-as-signedp timeout-secs print base-filename state)))

(defund prove-term-with-yices2 (term counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null timeout-secs) (natp timeout-secs))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state))
  (b* (((mv hyps conc) (term-hyps-and-conc term)))
    (prove-term-implication-with-yices2 conc hyps counterexamplep print-cex-as-signedp timeout-secs print base-filename state)))

(defund prove-term-with-yices2-unguarded (term counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
  (declare (xargs :stobjs state))
  (if (and (pseudo-termp term)
           (booleanp counterexamplep)
           (booleanp print-cex-as-signedp)
           (or (null timeout-secs) (natp timeout-secs))
           (print-levelp print)
           (stringp base-filename))
      (prove-term-with-yices2 term counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
    (prog2$ (er hard? 'prove-term-with-yices2-unguarded "Bad input.")
            (mv :error state))))

(defund translate-and-prove-term-with-yices2 (term counterexamplep print-cex-as-signedp timeout-secs print base-filename state)
  (declare (xargs :guard (and (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null timeout-secs) (natp timeout-secs))
                              (print-levelp print)
                              (stringp base-filename))
                  :mode :program
                  :stobjs state))
  (prove-term-with-yices2-unguarded (translate-term term 'translate-and-prove-term-with-yices2 (w state))
                                    counterexamplep print-cex-as-signedp timeout-secs print base-filename state))

(defmacro prove-with-yices2 (term
                                  &key
                                  (counterexample 't)
                                  (print-cex-as-signedp 'nil)
                                  (timeout-secs '*default-yices2-timeout-secs*)
                                  (print 'nil))
  `(translate-and-prove-term-with-yices2 ,term ',counterexample ',print-cex-as-signedp ,timeout-secs ',print
                                         "USER-QUERY"
                                         state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund prove-node-is-constant-with-yices2 (nodenum
                                            constant-value
                                            dag-array-name dag-array dag-len
                                            var-type-alist
                                            print
                                            timeout-secs
                                            proof-name
                                            state)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (symbolp proof-name))
                  :stobjs state))
  (b* ((needed-for-node1-tag-array (make-empty-array 'needed-for-node1-tag-array (+ 1 nodenum)))
       (needed-for-node1-tag-array (aset1 'needed-for-node1-tag-array needed-for-node1-tag-array nodenum t))
       ((mv erp nodenums-to-translate cut-nodenum-type-alist)
        (gather-nodes-for-translation nodenum dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nil nil))
       ((when (not (consp nodenums-to-translate)))
        (cw "ERROR: No nodes to translate.")
        (mv *error* state))
       ((when erp) (mv *error* state))
       ((mv result state)
        (prove-equality-with-yices2 (enquote constant-value)
                                    nodenum
                                    dag-array-name dag-array dag-len
                                    nodenums-to-translate
                                    (concatenate 'string (symbol-name proof-name) "-CONSTANT-" (nat-to-string nodenum))
                                    cut-nodenum-type-alist
                                    nil
                                    print
                                    timeout-secs
                                    nil
                                    nil
                                    state)))
    (if (eq *error* result)
        (prog2$ (er hard? 'prove-node-is-constant-with-yices2 "Error calling Yices2.")
                (mv result state))
      (if (eq *valid* result)
          (prog2$ (cw "Yices2 proved that node ~x0 is the constant ~x1.~%" nodenum constant-value)
                  (mv result state))
        (prog2$ (cw "Yices2 FAILED to prove that node ~x0 is the constant ~x1.~%" nodenum constant-value)
                (mv result state))))))

(defund try-aggressively-cut-equivalence-proof-with-yices2 (smaller-nodenum
                                                            larger-nodenum
                                                            dag-array-name
                                                            dag-array
                                                            dag-len
                                                            var-type-alist
                                                            print timeout-secs proof-name
                                                            state)
  (declare (xargs :guard (and (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (<= smaller-nodenum larger-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< smaller-nodenum dag-len)
                              (< larger-nodenum dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (symbolp proof-name))
                  :stobjs state))
  (b* ((- (and print (cw " (Cutting at shared nodes...")))
       ((mv erp nodenums-to-translate cut-nodenum-type-alist &)
        (gather-nodes-to-translate-for-aggressively-cut-proof2 (list larger-nodenum)
                                                               (list smaller-nodenum)
                                                               dag-array-name dag-array dag-len
                                                               var-type-alist
                                                               print
                                                               nil nil nil))
       (nodenums-to-translate (reverse-list nodenums-to-translate))
       ((when erp)
        (cw "ERROR (~x0) in gathering nodes.~%" erp)
        (mv erp nil nodenums-to-translate state))
       ((when (not (consp nodenums-to-translate)))
        (cw "ERROR: No nodes to translate.")
        (mv :no-nodes-to-translate nil nodenums-to-translate state))
       (- (and print (cw ")~%")))
       (- (and print (cw "  ~x0 nodes to translate.~%" (len nodenums-to-translate))))
       ((mv result state)
        (prove-equality-with-yices2 smaller-nodenum larger-nodenum
                                    dag-array-name dag-array dag-len
                                    nodenums-to-translate
                                    (n-string-append (symbol-name proof-name)
                                                     "-"
                                                     (nat-to-string smaller-nodenum)
                                                     "="
                                                     (nat-to-string larger-nodenum))
                                    cut-nodenum-type-alist
                                    nil
                                    print
                                    timeout-secs
                                    nil
                                    nil
                                    state)))
    (if (eq result *error*)
        (prog2$ (er hard? 'try-aggressively-cut-equivalence-proof-with-yices2 "Error calling Yices2." nil)
                (mv :error-calling-yices2 nil nodenums-to-translate state))
      (prog2$ (and (eq result *timedout*) (cw "Yices2 timed out.~%"))
              (mv (erp-nil)
                  (eq result *valid*)
                  nodenums-to-translate
                  state)))))

(defund try-cut-equivalence-proofs-with-yices2 (min-depth
                                                max-depth
                                                depth-array
                                                smaller-nodenum
                                                larger-nodenum
                                                dag-array-name dag-array dag-len
                                                var-type-alist print timeout-secs base-filename state)
  (declare (xargs :guard (and (natp min-depth)
                              (integerp max-depth)
                              (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (depth-arrayp 'depth-array depth-array (+ 1 larger-nodenum))
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (<= smaller-nodenum larger-nodenum)
                              (< larger-nodenum dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (stringp base-filename))
                  :measure (nfix (+ 1 (- max-depth min-depth)))
                  :stobjs state))
  (if (or (not (and (mbt (natp min-depth))
                    (mbt (integerp max-depth))))
          (< max-depth min-depth))
      (prog2$ (cw "!! We failed to find a cut depth at which Yices2 can prove the goal !!~%")
              (mv nil state))
    (b* ((supporters-tag-array (make-empty-array 'supporters-tag-array (+ 1 larger-nodenum)))
         (supporters-tag-array (aset1 'supporters-tag-array supporters-tag-array larger-nodenum t))
         (supporters-tag-array (aset1 'supporters-tag-array supporters-tag-array smaller-nodenum t))
         (current-depth min-depth)
         ((mv erp nodenums-to-translate cut-nodenum-type-alist &)
          (gather-nodes-to-translate-up-to-depth larger-nodenum current-depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array
                                                 nil
                                                 nil
                                                 nil))
         ((when erp) (mv nil state))
         ((when (not (consp nodenums-to-translate)))
          (cw "ERROR: No nodes to translate.")
          (mv nil state))
         (- (and print (cw "Attempting Yices2 proof at depth ~x0.~%" current-depth)))
         ((mv result state)
          (prove-equality-with-yices2 smaller-nodenum larger-nodenum
                                      dag-array-name dag-array dag-len
                                      nodenums-to-translate
                                      (string-append base-filename (nat-to-string current-depth))
                                      cut-nodenum-type-alist
                                      nil
                                      print
                                      timeout-secs
                                      nil
                                      nil
                                      state))
         ((when (eq result *error*))
          (er hard? 'try-cut-equivalence-proofs-with-yices2 "Error calling Yices2." nil)
          (mv nil state)))
      (if (eq result *valid*)
          (mv t state)
        (if (eq result *timedout*)
            (mv nil state)
          (try-cut-equivalence-proofs-with-yices2 (+ 1 current-depth) max-depth
                                                  depth-array
                                                  smaller-nodenum larger-nodenum
                                                  dag-array-name dag-array dag-len
                                                  var-type-alist print timeout-secs base-filename state))))))

(defun try-to-prove-pure-nodes-equal-with-yices2 (smaller-nodenum
                                                  larger-nodenum
                                                  miter-array-name miter-array miter-len
                                                  var-type-alist
                                                  print timeout-secs proof-name state)
  (declare (xargs :guard (and (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (<= smaller-nodenum larger-nodenum)
                              (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                              (< smaller-nodenum miter-len)
                              (< larger-nodenum miter-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (or (null timeout-secs) (natp timeout-secs))
                              (symbolp proof-name))
                  :stobjs state))
  (b* ((- (cw "(Attempting aggressively cut proof with Yices2:~%"))
       ((mv erp provedp nodenums-translated state)
        (try-aggressively-cut-equivalence-proof-with-yices2 smaller-nodenum larger-nodenum miter-array-name miter-array miter-len var-type-alist print timeout-secs proof-name state))
       ((when erp)
        (cw "  ERROR.)~%")
        (mv nil state))
       (- (if provedp
              (cw "  Proved.)~%")
            (cw "  Failed.)~%")))
       ((when provedp) (mv t state))
       ((mv depth-array max-depth)
        (make-depth-array-for-nodes (list smaller-nodenum larger-nodenum) miter-array-name miter-array miter-len))
       (depth-of-deepest-translated-node (max-array-elem2 nodenums-translated 0 'depth-array depth-array))
       (- (cw "(Attempting cut proofs with Yices2 (min-depth ~x0, max-depth ~x1):~%" depth-of-deepest-translated-node max-depth))
       ((mv success-flg state)
        (try-cut-equivalence-proofs-with-yices2 depth-of-deepest-translated-node
                                                max-depth
                                                depth-array
                                                smaller-nodenum
                                                larger-nodenum
                                                miter-array-name
                                                miter-array
                                                miter-len
                                                var-type-alist
                                                print
                                                timeout-secs
                                                (n-string-append (symbol-name proof-name)
                                                                 "-"
                                                                 (nat-to-string smaller-nodenum)
                                                                 "="
                                                                 (nat-to-string larger-nodenum)
                                                                 "-depth-")
                                                state))
       (- (cw ")")))
    (mv (if success-flg
            t
          (prog2$ (cw "!! Yices2 failed to prove the equality of nodes ~x0 and ~x1. !!~%" smaller-nodenum larger-nodenum)
                  nil))
        state)))

(set-verify-guards-eagerness 2)
