(RP::RP-EQUAL-META)
(RP::RP-EQUAL-CNT-META)
(RP::RP-EQUAL-META_FOR_EQUAL_VALID
 (2272 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
 (2197 1 (:DEFINITION RP::RP-EQUAL2))
 (2141 8 (:DEFINITION RP::RP-EQUAL))
 (2086 49 (:DEFINITION RP::EX-FROM-RP))
 (1988 5 (:REWRITE RP::RP-EQUAL-IMPLIES-RP-EQUAL2))
 (1039 937 (:REWRITE DEFAULT-CDR))
 (1004 800 (:REWRITE DEFAULT-CAR))
 (709 2 (:DEFINITION RP::VALID-SC))
 (659 56 (:REWRITE RP::NOT-INCLUDE-RP))
 (614 66 (:DEFINITION RP::INCLUDE-FNC))
 (612 34 (:DEFINITION RP::TRANS-LIST))
 (330 330 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (306 306 (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
 (276 2 (:DEFINITION RP::EVAL-AND-ALL))
 (275 64 (:REWRITE RP::IS-IF-RP-TERMP))
 (250 16 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (180 180 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (173 38 (:REWRITE RP::RP-TERMP-CADR))
 (146 26 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (142 16 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (136 136 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (133 11 (:DEFINITION RP::IS-SYNP$INLINE))
 (127 10 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
 (114 114 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
 (106 26 (:REWRITE RP::RP-TERMP-CADDR))
 (102 102 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (92 2 (:REWRITE RP::EXTRACT-FROM-SYNP-TO-EX-FROM-RP))
 (90 2 (:DEFINITION RP::EX-FROM-SYNP))
 (82 26 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (82 6 (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
 (78 26 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (62 2 (:REWRITE RP::NOT-INCLUDE-SYNP))
 (60 60 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (50 10 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (36 6 (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
 (34 2 (:DEFINITION RP::SHOULD-TERM-BE-IN-CONS$INLINE))
 (30 10 (:DEFINITION APPLY$-BADGEP))
 (26 26 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (26 7 (:REWRITE RP::VALID-SC-CADR))
 (26 2 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
 (24 8 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (20 10 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (20 2 (:REWRITE RP::VALID-SC-EX-FROM-RP))
 (20 1 (:REWRITE RP::RP-EQUAL-SUBTERMS-IMPLIES-RP-EQUAL2-SUBTERMS))
 (18 18 (:TYPE-PRESCRIPTION QUOTEP))
 (18 9 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
 (18 2 (:DEFINITION RP::IS-CONS$INLINE))
 (15 1 (:DEFINITION RP::RP-EQUAL-SUBTERMS))
 (14 2 (:DEFINITION RP::PUT-TERM-IN-CONS$INLINE))
 (14 2 (:DEFINITION RP::IS-QUOTED-PAIR$INLINE))
 (13 13 (:TYPE-PRESCRIPTION RP::RP-EQUAL2))
 (13 5 (:REWRITE RP::VALID-SC-CADDR))
 (12 12 (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
 (12 10 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BADGE-USERFN-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-APPLY$-USERFN-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-APPLY$-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (12 6 (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
 (10 10 (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
 (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (10 5 (:REWRITE RP::RP-EQUAL2-REFLEXIVE))
 (10 2 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
 (10 2 (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
 (9 9 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (8 8 (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
 (7 7 (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
 (4 4 (:REWRITE RP::SHOULD-TERM-BE-IN-CONS-LEMMA2))
 (3 1 (:REWRITE RP::VALID-SC-CADDDR))
 (2 2 (:TYPE-PRESCRIPTION RP::RP-EQUAL2-SUBTERMS))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (2 2 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
 (2 2 (:REWRITE RP::RP-TERMP-OF-RP-TRANS))
 (2 2 (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
 (2 1 (:REWRITE RP::RP-EQUAL2-SUBTERMS-REFLEXIVE))
 (1 1 (:REWRITE RP::VALID-SC-NIL))
 )
(RP::RP-EQUAL-CNT-META_FOR_EQUAL_VALID
 (2272 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
 (2197 1 (:DEFINITION RP::RP-EQUAL2))
 (2141 8 (:DEFINITION RP::RP-EQUAL))
 (2086 49 (:DEFINITION RP::EX-FROM-RP))
 (1988 5 (:REWRITE RP::RP-EQUAL-IMPLIES-RP-EQUAL2))
 (1039 937 (:REWRITE DEFAULT-CDR))
 (1004 800 (:REWRITE DEFAULT-CAR))
 (709 2 (:DEFINITION RP::VALID-SC))
 (659 56 (:REWRITE RP::NOT-INCLUDE-RP))
 (614 66 (:DEFINITION RP::INCLUDE-FNC))
 (612 34 (:DEFINITION RP::TRANS-LIST))
 (330 330 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (306 306 (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
 (276 2 (:DEFINITION RP::EVAL-AND-ALL))
 (275 64 (:REWRITE RP::IS-IF-RP-TERMP))
 (250 16 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (180 180 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (173 38 (:REWRITE RP::RP-TERMP-CADR))
 (146 26 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (142 16 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (136 136 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (133 11 (:DEFINITION RP::IS-SYNP$INLINE))
 (127 10 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
 (114 114 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
 (106 26 (:REWRITE RP::RP-TERMP-CADDR))
 (102 102 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (92 2 (:REWRITE RP::EXTRACT-FROM-SYNP-TO-EX-FROM-RP))
 (90 2 (:DEFINITION RP::EX-FROM-SYNP))
 (82 26 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (82 6 (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
 (78 26 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (62 2 (:REWRITE RP::NOT-INCLUDE-SYNP))
 (60 60 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (50 10 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (36 6 (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
 (34 2 (:DEFINITION RP::SHOULD-TERM-BE-IN-CONS$INLINE))
 (30 10 (:DEFINITION APPLY$-BADGEP))
 (26 26 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (26 7 (:REWRITE RP::VALID-SC-CADR))
 (26 2 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
 (24 8 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (20 10 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (20 2 (:REWRITE RP::VALID-SC-EX-FROM-RP))
 (20 1 (:REWRITE RP::RP-EQUAL-SUBTERMS-IMPLIES-RP-EQUAL2-SUBTERMS))
 (18 18 (:TYPE-PRESCRIPTION QUOTEP))
 (18 9 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
 (18 2 (:DEFINITION RP::IS-CONS$INLINE))
 (15 1 (:DEFINITION RP::RP-EQUAL-SUBTERMS))
 (14 2 (:DEFINITION RP::PUT-TERM-IN-CONS$INLINE))
 (14 2 (:DEFINITION RP::IS-QUOTED-PAIR$INLINE))
 (13 13 (:TYPE-PRESCRIPTION RP::RP-EQUAL2))
 (13 5 (:REWRITE RP::VALID-SC-CADDR))
 (12 12 (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
 (12 10 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BADGE-USERFN-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-APPLY$-USERFN-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-APPLY$-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (12 10 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (12 6 (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
 (10 10 (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
 (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (10 5 (:REWRITE RP::RP-EQUAL2-REFLEXIVE))
 (10 2 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
 (10 2 (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
 (9 9 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (8 8 (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
 (7 7 (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
 (4 4 (:REWRITE RP::SHOULD-TERM-BE-IN-CONS-LEMMA2))
 (3 1 (:REWRITE RP::VALID-SC-CADDDR))
 (2 2 (:TYPE-PRESCRIPTION RP::RP-EQUAL2-SUBTERMS))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (2 2 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
 (2 2 (:REWRITE RP::RP-TERMP-OF-RP-TRANS))
 (2 2 (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
 (2 1 (:REWRITE RP::RP-EQUAL2-SUBTERMS-REFLEXIVE))
 (1 1 (:REWRITE RP::VALID-SC-NIL))
 )
