(STVDATA-P
 (4 4 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(STVDATA)
(HONSED-STVDATA)
(STVDATA->INPUTS$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(STVDATA->OUTPUTS$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(STVDATA->INTERNALS$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(STVDATA->OVERRIDES$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-STVDATA)
(BOOLEANP-OF-STVDATA-P)
(STVDATA-P-OF-STVDATA)
(TAG-OF-STVDATA)
(TAG-WHEN-STVDATA-P)
(STVDATA-P-WHEN-WRONG-TAG)
(CONSP-WHEN-STVDATA-P)
(STVDATA->INPUTS-OF-STVDATA)
(STVDATA->OUTPUTS-OF-STVDATA)
(STVDATA->INTERNALS-OF-STVDATA)
(STVDATA->OVERRIDES-OF-STVDATA)
(RETURN-TYPE-OF-STVDATA->INPUTS)
(RETURN-TYPE-OF-STVDATA->OUTPUTS)
(RETURN-TYPE-OF-STVDATA->INTERNALS)
(RETURN-TYPE-OF-STVDATA->OVERRIDES)
(COMPILED-STV-P
 (10 10 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(COMPILED-STV)
(HONSED-COMPILED-STV)
(COMPILED-STV->NPHASES$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->NST-EXTRACT-ALISTS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->OUT-EXTRACT-ALISTS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->INT-EXTRACT-ALISTS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->OVERRIDE-BITS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->RESTRICT-ALIST$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->IN-USERSYMS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->OUT-USERSYMS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->EXPANDED-INS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(COMPILED-STV->OVERRIDE-PATHS$INLINE
 (6 6 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-COMPILED-STV)
(BOOLEANP-OF-COMPILED-STV-P)
(COMPILED-STV-P-OF-COMPILED-STV)
(TAG-OF-COMPILED-STV)
(TAG-WHEN-COMPILED-STV-P)
(COMPILED-STV-P-WHEN-WRONG-TAG)
(CONSP-WHEN-COMPILED-STV-P)
(COMPILED-STV->NPHASES-OF-COMPILED-STV)
(COMPILED-STV->NST-EXTRACT-ALISTS-OF-COMPILED-STV)
(COMPILED-STV->OUT-EXTRACT-ALISTS-OF-COMPILED-STV)
(COMPILED-STV->INT-EXTRACT-ALISTS-OF-COMPILED-STV)
(COMPILED-STV->OVERRIDE-BITS-OF-COMPILED-STV)
(COMPILED-STV->RESTRICT-ALIST-OF-COMPILED-STV)
(COMPILED-STV->IN-USERSYMS-OF-COMPILED-STV)
(COMPILED-STV->OUT-USERSYMS-OF-COMPILED-STV)
(COMPILED-STV->EXPANDED-INS-OF-COMPILED-STV)
(COMPILED-STV->OVERRIDE-PATHS-OF-COMPILED-STV)
(RETURN-TYPE-OF-COMPILED-STV->NPHASES)
(RETURN-TYPE-OF-COMPILED-STV->NST-EXTRACT-ALISTS)
(RETURN-TYPE-OF-COMPILED-STV->OUT-EXTRACT-ALISTS)
(RETURN-TYPE-OF-COMPILED-STV->INT-EXTRACT-ALISTS)
(RETURN-TYPE-OF-COMPILED-STV->OVERRIDE-BITS)
(RETURN-TYPE-OF-COMPILED-STV->OVERRIDE-PATHS)
(PROCESSED-STV-P
 (4 4 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(PROCESSED-STV)
(HONSED-PROCESSED-STV)
(PROCESSED-STV->NAME$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(PROCESSED-STV->USER-STV$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(PROCESSED-STV->COMPILED-STV$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(PROCESSED-STV->RELEVANT-SIGNALS$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-PROCESSED-STV)
(BOOLEANP-OF-PROCESSED-STV-P)
(PROCESSED-STV-P-OF-PROCESSED-STV)
(TAG-OF-PROCESSED-STV)
(TAG-WHEN-PROCESSED-STV-P)
(PROCESSED-STV-P-WHEN-WRONG-TAG)
(CONSP-WHEN-PROCESSED-STV-P)
(PROCESSED-STV->NAME-OF-PROCESSED-STV)
(PROCESSED-STV->USER-STV-OF-PROCESSED-STV)
(PROCESSED-STV->COMPILED-STV-OF-PROCESSED-STV)
(PROCESSED-STV->RELEVANT-SIGNALS-OF-PROCESSED-STV)
(RETURN-TYPE-OF-PROCESSED-STV->NAME)
(RETURN-TYPE-OF-PROCESSED-STV->COMPILED-STV)
(ORDERED-SUBSETP)
(STV-MAX-PHASES-IN-LINES
 (48 8 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (40 4 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (20 5 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (18 18 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (10 10 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (10 10 (:TYPE-PRESCRIPTION ALISTP))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8 (:REWRITE SET::IN-SET))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (8 1 (:REWRITE ALISTP-OF-CDR))
 (5 5 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (5 5 (:REWRITE ALISTP-WHEN-ATOM))
 )
(NATP-OF-STV-MAX-PHASES-IN-LINES)
(STV-NUMBER-OF-PHASES
 (12 3 (:REWRITE DEFAULT-<-1))
 (11 5 (:REWRITE STVDATA-P-WHEN-WRONG-TAG))
 (6 3 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE TAG-WHEN-STVDATA-P))
 (2 1 (:REWRITE TAG-WHEN-PROCESSED-STV-P))
 (2 1 (:REWRITE TAG-WHEN-COMPILED-STV-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-PROCESSED-STV-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-COMPILED-STV-P))
 )
(NATP-OF-STV-NUMBER-OF-PHASES)
(STV-SUFFIX-SIGNALS
 (46 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (43 1 (:DEFINITION BINARY-APPEND))
 (30 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (20 6 (:REWRITE STR::CONSP-OF-EXPLODE))
 (16 16 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (10 1 (:DEFINITION MEMBER-EQUAL))
 (8 4 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE SUBSETP-MEMBER . 2))
 (7 7 (:REWRITE SUBSETP-MEMBER . 1))
 (7 3 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE MEMBER-SELF))
 (3 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (1 1 (:REWRITE ATOM-LISTP-WHEN-NOT-CONSP))
 )
(SYMBOL-LISTP-OF-STV-SUFFIX-SIGNALS
 (130 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (78 6 (:DEFINITION MEMBER-EQUAL))
 (42 1 (:DEFINITION BINARY-APPEND))
 (34 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (21 16 (:REWRITE DEFAULT-CDR))
 (21 16 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE FN-CHECK-DEF-FORMALS))
 (16 4 (:REWRITE STR::CONSP-OF-EXPLODE))
 (12 12 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (12 12 (:TYPE-PRESCRIPTION STRINGIFY))
 (12 12 (:REWRITE SUBSETP-MEMBER . 2))
 (12 12 (:REWRITE SUBSETP-MEMBER . 1))
 (4 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (3 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 1 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 )
(SAFE-PAIRLIS-ONTO-ACC
 (569 21 (:DEFINITION BINARY-APPEND))
 (366 366 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (211 80 (:REWRITE CONSP-OF-REV))
 (104 19 (:REWRITE REV-WHEN-NOT-CONSP))
 (4 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(STV->INS)
(STV->OUTS)
(STV->VARS)
(STV-OUT->WIDTH
 (8 2 (:REWRITE PROCESSED-STV-P-WHEN-WRONG-TAG))
 (3 1 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:REWRITE TAG-WHEN-STVDATA-P))
 (2 1 (:REWRITE TAG-WHEN-PROCESSED-STV-P))
 (2 1 (:REWRITE TAG-WHEN-COMPILED-STV-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-STVDATA-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-COMPILED-STV-P))
 )
(NATP-OF-STV-OUT->WIDTH)
(STV-IN->WIDTH
 (8 2 (:REWRITE PROCESSED-STV-P-WHEN-WRONG-TAG))
 (3 1 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:REWRITE TAG-WHEN-STVDATA-P))
 (2 1 (:REWRITE TAG-WHEN-PROCESSED-STV-P))
 (2 1 (:REWRITE TAG-WHEN-COMPILED-STV-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-STVDATA-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-COMPILED-STV-P))
 )
(NATP-OF-STV-IN->WIDTH)
