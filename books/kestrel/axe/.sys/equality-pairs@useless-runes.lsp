(EQUALITY-PAIRP)
(ALL-EQUALITY-PAIRP)
(ALL-EQUALITY-PAIRP-OF-CONS)
(USE-ALL-EQUALITY-PAIRP-FOR-CAR)
(USE-ALL-EQUALITY-PAIRP-FOR-CAR-OF-LAST)
(ALL-EQUALITY-PAIRP-OF-APPEND)
(ALL-EQUALITY-PAIRP-OF-UNION-EQUAL)
(ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP)
(ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP)
(ALL-EQUALITY-PAIRP-OF-REVAPPEND)
(ALL-EQUALITY-PAIRP-OF-CDR)
(ALL-EQUALITY-PAIRP-OF-NTHCDR)
(ALL-EQUALITY-PAIRP-OF-FIRSTN)
(ALL-EQUALITY-PAIRP-OF-REMOVE1-EQUAL)
(ALL-EQUALITY-PAIRP-OF-REMOVE-EQUAL)
(ALL-EQUALITY-PAIRP-OF-LAST)
(ALL-EQUALITY-PAIRP-OF-TAKE)
(ALL-EQUALITY-PAIRP-WHEN-PERM)
(ALL-EQUALITY-PAIRP-OF-TRUE-LIST-FIX)
(PERM-IMPLIES-EQUAL-ALL-EQUALITY-PAIRP-1)
(USE-ALL-EQUALITY-PAIRP)
(USE-ALL-EQUALITY-PAIRP-2)
(ALL-EQUALITY-PAIRP-OF-ADD-TO-SET-EQUAL)
(EQUALITY-PAIRSP)
(PSEUDO-TERMP-OF-CAR-OF-CAR-WHEN-EQUALITY-PAIRSP
 (118 2 (:DEFINITION PSEUDO-TERMP))
 (34 30 (:REWRITE DEFAULT-CAR))
 (34 6 (:DEFINITION LEN))
 (30 30 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:DEFINITION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 2 (:DEFINITION SYMBOL-LISTP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 )
(ADD-EQUALITY-PAIRS-FOR-ASSUMPTION
 (462 220 (:REWRITE DEFAULT-+-2))
 (279 279 (:REWRITE DEFAULT-CDR))
 (278 220 (:REWRITE DEFAULT-+-1))
 (182 182 (:REWRITE DEFAULT-CAR))
 (128 32 (:REWRITE COMMUTATIVITY-OF-+))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (82 41 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (51 40 (:REWRITE DEFAULT-<-2))
 (48 40 (:REWRITE DEFAULT-<-1))
 (41 41 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 8 (:DEFINITION TRUE-LISTP))
 (25 25 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (25 25 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(EQUALITY-PAIRSP-OF-ADD-EQUALITY-PAIRS-FOR-ASSUMPTION
 (729 729 (:REWRITE DEFAULT-CDR))
 (662 658 (:REWRITE DEFAULT-CAR))
 (246 123 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (216 70 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (210 105 (:REWRITE DEFAULT-+-2))
 (206 74 (:DEFINITION TRUE-LISTP))
 (145 29 (:DEFINITION SYMBOL-LISTP))
 (123 123 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (106 106 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (105 105 (:REWRITE DEFAULT-+-1))
 (97 97 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (73 70 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (21 7 (:REWRITE USE-ALL-EQUALITY-PAIRP))
 (14 14 (:TYPE-PRESCRIPTION MEMBERP))
 (7 7 (:REWRITE USE-ALL-EQUALITY-PAIRP-2))
 )
(ADD-EQUALITY-PAIRS-FOR-ASSUMPTIONS
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(EQUALITY-PAIRSP-OF-ADD-EQUALITY-PAIRS-FOR-ASSUMPTIONS
 (301 7 (:DEFINITION ADD-EQUALITY-PAIRS-FOR-ASSUMPTION))
 (284 4 (:DEFINITION PSEUDO-TERMP))
 (177 177 (:REWRITE DEFAULT-CDR))
 (154 154 (:REWRITE DEFAULT-CAR))
 (103 19 (:DEFINITION LEN))
 (71 71 (:TYPE-PRESCRIPTION LEN))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (42 14 (:DEFINITION MEMBER-EQUAL))
 (38 19 (:REWRITE DEFAULT-+-2))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 7 (:DEFINITION QUOTEP))
 (26 4 (:DEFINITION SYMBOL-LISTP))
 (23 23 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 4 (:DEFINITION TRUE-LISTP))
 (19 19 (:REWRITE DEFAULT-+-1))
 (17 17 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(MAKE-EQUALITY-PAIRS)
(EQUALITY-PAIRSP-OF-MAKE-EQUALITY-PAIRS)
