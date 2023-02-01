(PFCS::R1CS-VEC-ELEM-TO-PFCS
 (142 8 (:REWRITE R1CS::PSEUDO-VAR-LISTP-FORWARD-TO-TRUE-LISTP))
 (118 8 (:REWRITE R1CS::PSEUDO-VAR-LISTP-WHEN-SYMBOL-LISTP))
 (80 16 (:DEFINITION SYMBOL-LISTP))
 (64 8 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (57 15 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (52 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (46 4 (:DEFINITION INTEGER-LISTP))
 (32 32 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE DEFAULT-CAR))
 (24 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (22 22 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 16 (:TYPE-PRESCRIPTION R1CS::PSEUDO-VAR-LISTP))
 (16 8 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 6 (:REWRITE DEFAULT-+-2))
 (10 5 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8 (:REWRITE SET::IN-SET))
 (7 7 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(PFCS::EXPRESSIONP-OF-R1CS-VEC-ELEM-TO-PFCS)
(PFCS::R1CS-MONOMIALP-OF-R1CS-VEC-ELEM-TO-PFCS
 (20 20 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE PFCS::EXPRESSION-CASE-WHEN-MEMBER-EQUAL-OF-EXPRESSION-VAR-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
(PFCS::R1CS-VECTOR-TO-PFCS-AUX
 (2013 54 (:REWRITE R1CS::PSEUDO-VAR-LISTP-FORWARD-TO-TRUE-LISTP))
 (1848 54 (:REWRITE R1CS::PSEUDO-VAR-LISTP-WHEN-SYMBOL-LISTP))
 (1708 136 (:DEFINITION SYMBOL-LISTP))
 (1450 216 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (786 5 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (780 3 (:DEFINITION TRUE-LIST-LISTP))
 (730 137 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (432 54 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (391 391 (:REWRITE DEFAULT-CAR))
 (342 40 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (332 332 (:REWRITE DEFAULT-CDR))
 (313 313 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (301 24 (:DEFINITION INTEGER-LISTP))
 (108 108 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (108 54 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (108 54 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (101 101 (:TYPE-PRESCRIPTION R1CS::PSEUDO-VAR-LISTP))
 (76 38 (:REWRITE DEFAULT-+-2))
 (62 31 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (54 54 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (54 54 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (54 54 (:REWRITE SET::IN-SET))
 (44 44 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (38 38 (:REWRITE DEFAULT-+-1))
 (30 5 (:REWRITE R1CS::PSEUDO-VAR-LISTP-OF-CONS))
 (6 3 (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (5 5 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SYMBOL-LISTP-OF-CONS))
 )
(PFCS::EXPRESSIONP-OF-R1CS-VECTOR-TO-PFCS-AUX
 (9 9 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(PFCS::R1CS-POLYNOMIALP-OF-R1CS-VECTOR-TO-PFCS-AUX
 (8 8 (:REWRITE PFCS::EXPRESSION-CASE-WHEN-MEMBER-EQUAL-OF-EXPRESSION-VAR-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION PFCS::EXPRESSION-KIND$INLINE))
 (6 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(PFCS::R1CS-VECTOR-TO-PFCS)
(PFCS::EXPRESSIONP-OF-R1CS-VECTOR-TO-PFCS)
(PFCS::R1CS-POLYNOMIALP-OF-R1CS-VECTOR-TO-PFCS)
(PFCS::R1CS-CONSTRAINT-TO-PFCS)
(PFCS::CONSTRAINTP-OF-R1CS-CONSTRAINT-TO-PFCS)
(PFCS::R1CS-CONSTRAINTP-OF-R1CS-CONSTRAINT-TO-PFCS
 (2 2 (:REWRITE PFCS::EXPRESSION-CASE-WHEN-MEMBER-EQUAL-OF-EXPRESSION-VAR-LISTP))
 )
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-EXEC)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-NREV)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::CONSTRAINT-LISTP-OF-R1CS-CONSTRAINTS-TO-PFCS
 (33 9 (:REWRITE PFCS::CONSTRAINT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-NIL-PRESERVINGP-LEMMA)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-OF-TAKE
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(PFCS::SET-EQUIV-CONGRUENCE-OVER-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::SUBSETP-OF-R1CS-CONSTRAINTS-TO-PFCS-WHEN-SUBSETP)
(PFCS::MEMBER-OF-R1CS-CONSTRAINT-TO-PFCS-IN-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-NREV-REMOVAL
 (238 5 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (162 6 (:REWRITE R1CS::PSEUDO-VAR-LISTP-FORWARD-TO-TRUE-LISTP))
 (147 3 (:DEFINITION TRUE-LISTP))
 (144 6 (:REWRITE R1CS::PSEUDO-VAR-LISTP-WHEN-SYMBOL-LISTP))
 (108 9 (:DEFINITION SYMBOL-LISTP))
 (66 12 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (48 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (36 3 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (27 9 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (21 21 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (20 20 (:REWRITE DEFAULT-CDR))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (15 3 (:DEFINITION LEN))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:TYPE-PRESCRIPTION R1CS::PSEUDO-VAR-LISTP))
 (12 6 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION TYPE-OF-RCONS))
 )
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-EXEC-REMOVAL
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-OF-REV)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-OF-LIST-FIX)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-OF-APPEND)
(PFCS::CDR-OF-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::CAR-OF-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-UNDER-IFF)
(PFCS::CONSP-OF-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::LEN-OF-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::TRUE-LISTP-OF-R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-WHEN-NOT-CONSP)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-OF-CONS)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-NREV
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(PFCS::R1CS-CONSTRAINTS-TO-PFCS)
(PFCS::R1CS-CONSTRAINTS-TO-PFCS-EXEC
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(PFCS::R1CS-CONSTRAINT-LISTP-OF-R1CS-CONSTRAINTS-TO-PFCS
 (89 1 (:REWRITE SUBSETP-OF-CONS))
 (59 2 (:DEFINITION MEMBER-EQUAL))
 (40 2 (:REWRITE PFCS::MEMBER-OF-R1CS-CONSTRAINT-TO-PFCS-IN-R1CS-CONSTRAINTS-TO-PFCS))
 (22 6 (:REWRITE PFCS::R1CS-CONSTRAINT-LISTP-WHEN-NOT-CONSP))
 (21 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (14 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (12 12 (:TYPE-PRESCRIPTION PFCS::R1CS-CONSTRAINT-TO-PFCS))
 (11 11 (:REWRITE SUBSETP-TRANS2))
 (11 11 (:REWRITE SUBSETP-TRANS))
 (10 10 (:REWRITE PFCS::CONSP-OF-R1CS-CONSTRAINTS-TO-PFCS))
 (8 2 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (7 5 (:REWRITE DEFAULT-CDR))
 (7 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE SUBSETP-MEMBER . 2))
 (5 5 (:REWRITE SUBSETP-MEMBER . 1))
 (5 5 (:REWRITE PFCS::R1CS-CONSTRAINTS-TO-PFCS-WHEN-NOT-CONSP))
 (3 1 (:REWRITE PFCS::CDR-OF-R1CS-CONSTRAINTS-TO-PFCS))
 (2 1 (:REWRITE PFCS::CAR-OF-R1CS-CONSTRAINTS-TO-PFCS))
 (1 1 (:REWRITE PFCS::R1CS-CONSTRAINTS-TO-PFCS-UNDER-IFF))
 )
(PFCS::R1CS-TO-PFCS)
(PFCS::SYSTEMP-OF-R1CS-TO-PFCS)
(PFCS::R1CS-SYSTEMP-OF-R1CS-TO-PFCS
 (1 1 (:REWRITE PFCS::R1CS-CONSTRAINTS-TO-PFCS-WHEN-NOT-CONSP))
 )
