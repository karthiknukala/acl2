(PFCS::YYYJOIN)
(PFCS::CONSTRAINT/CONSTRAINTLIST-P)
(PFCS::BOOLEANP-OF-CONSTRAINT/CONSTRAINTLIST-P)
(PFCS::CONSTRAINT/CONSTRAINTLIST-P-WHEN-CONSTRAINTP)
(PFCS::CONSTRAINT/CONSTRAINTLIST-P-WHEN-CONSTRAINT-LISTP)
(PFCS::NOT-CONSTRAINTP-WHEN-CONSTRAINT-LISTP
 (60 6 (:REWRITE PFCS::EXPRESSIONP-OF-CAR-WHEN-EXPRESSION-LISTP))
 (36 9 (:REWRITE PFCS::EXPRESSION-LISTP-OF-CDR-WHEN-EXPRESSION-LISTP))
 (18 18 (:REWRITE PFCS::EXPRESSION-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE PFCS::CONSTRAINT-LISTP-WHEN-NOT-CONSP))
 )
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-OF-CONS)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-OF-CDR-WHEN-CONSTRAINT/CONSTRAINTLIST-LISTP)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-WHEN-NOT-CONSP)
(PFCS::CONSTRAINT/CONSTRAINTLIST-P-OF-CAR-WHEN-CONSTRAINT/CONSTRAINTLIST-LISTP)
(PFCS::TRUE-LISTP-WHEN-CONSTRAINT/CONSTRAINTLIST-LISTP-COMPOUND-RECOGNIZER)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-OF-LIST-FIX)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-OF-REV)
(PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-OF-APPEND)
(PFCS::PFDEF-JOIN
 (17 8 (:REWRITE PFCS::CONSTRAINTP-OF-CAR-WHEN-CONSTRAINT-LISTP))
 (10 10 (:REWRITE PFCS::CONSTRAINT-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE PFCS::CONSTRAINT/CONSTRAINTLIST-LISTP-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE PFCS::CONSTRAINT/CONSTRAINTLIST-P-WHEN-CONSTRAINTP))
 (1 1 (:REWRITE PFCS::CONSTRAINT/CONSTRAINTLIST-P-WHEN-CONSTRAINT-LISTP))
 )
(PFCS::CONSTRAINT-LISTP-OF-PFDEF-JOIN
 (87 38 (:REWRITE PFCS::CONSTRAINT-LISTP-WHEN-NOT-CONSP))
 (49 13 (:REWRITE PFCS::CONSTRAINTP-OF-CAR-WHEN-CONSTRAINT-LISTP))
 (1 1 (:REWRITE APPEND-WHEN-NOT-CONSP))
 )
