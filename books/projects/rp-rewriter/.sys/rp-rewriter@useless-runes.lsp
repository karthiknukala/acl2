(RP::REMOVE-RP-FROM-BINDINGS
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(RP::QUOTE-LISTP)
(RP::RP-APPLY-BINDINGS)
(RP::RP-MATCH-LHS
 (132 6 (:DEFINITION LENGTH))
 (121 58 (:REWRITE DEFAULT-+-2))
 (111 39 (:REWRITE RP::IS-RP-IMPLIES))
 (108 6 (:DEFINITION LEN))
 (81 58 (:REWRITE DEFAULT-+-1))
 (72 72 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (54 18 (:REWRITE DEFAULT-CDR))
 (48 12 (:REWRITE COMMUTATIVITY-OF-+))
 (48 12 (:DEFINITION INTEGER-ABS))
 (24 12 (:REWRITE STR::CONSP-OF-EXPLODE))
 (18 18 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (17 14 (:REWRITE DEFAULT-<-2))
 (16 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 6 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (6 6 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 6 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (6 6 (:REWRITE DEFAULT-REALPART))
 (6 6 (:REWRITE DEFAULT-NUMERATOR))
 (6 6 (:REWRITE DEFAULT-IMAGPART))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (3 3 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 )
(RP::RP-DOES-LHS-MATCH
 (276 102 (:REWRITE RP::IS-RP-IMPLIES))
 (132 6 (:DEFINITION LENGTH))
 (121 58 (:REWRITE DEFAULT-+-2))
 (108 6 (:DEFINITION LEN))
 (89 46 (:REWRITE DEFAULT-CDR))
 (81 58 (:REWRITE DEFAULT-+-1))
 (79 1 (:DEFINITION RP::RP-TERMP))
 (48 12 (:REWRITE COMMUTATIVITY-OF-+))
 (48 12 (:DEFINITION INTEGER-ABS))
 (47 43 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE STR::CONSP-OF-EXPLODE))
 (18 18 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (17 14 (:REWRITE DEFAULT-<-2))
 (16 16 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (16 14 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 6 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (12 3 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (8 2 (:REWRITE RP::RP-TERMP-CADR))
 (8 2 (:REWRITE RP::RP-TERMP-CADDR))
 (7 2 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (6 6 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 6 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (6 6 (:REWRITE DEFAULT-REALPART))
 (6 6 (:REWRITE DEFAULT-NUMERATOR))
 (6 6 (:REWRITE DEFAULT-IMAGPART))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (3 3 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 )
(RP::RP-MATCH-LHS-PRECHECK$INLINE)
(RP::RP-CHECK-CONTEXT-FN)
(RP::RP-GET-DONT-RW
 (58 28 (:REWRITE DEFAULT-+-2))
 (48 3 (:DEFINITION LENGTH))
 (39 28 (:REWRITE DEFAULT-+-1))
 (36 3 (:DEFINITION LEN))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (18 9 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE STR::CONSP-OF-EXPLODE))
 (9 9 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (9 7 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (4 4 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (3 3 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (3 3 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (3 3 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (3 3 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::UNQUOTE-ALL)
(RP::MAGIC-EV-FNCALL-WRAPPER)
(RP::RP-EX-COUNTERPART
 (190 190 (:REWRITE DEFAULT-CAR))
 (177 177 (:REWRITE DEFAULT-CDR))
 (90 15 (:DEFINITION ASSOC-EQUAL))
 (46 1 (:DEFINITION RP::RP-TERMP))
 (37 37 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (30 15 (:DEFINITION NTH))
 (26 26 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (26 26 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (12 12 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (10 10 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (8 2 (:REWRITE RP::RP-TERMP-CADR))
 (8 2 (:REWRITE RP::RP-TERMP-CADDR))
 (7 2 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (4 1 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (1 1 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (1 1 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (1 1 (:REWRITE MEXTRACT-FNCALL))
 )
(RP::RP-EXTRACT-CONTEXT
 (571 313 (:REWRITE DEFAULT-+-2))
 (399 313 (:REWRITE DEFAULT-+-1))
 (384 24 (:DEFINITION LENGTH))
 (368 296 (:REWRITE DEFAULT-CDR))
 (349 45 (:DEFINITION APPLY$-BADGEP))
 (288 24 (:DEFINITION LEN))
 (277 31 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (192 48 (:DEFINITION INTEGER-ABS))
 (163 25 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (162 45 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (161 161 (:REWRITE DEFAULT-CAR))
 (96 48 (:REWRITE STR::CONSP-OF-EXPLODE))
 (94 7 (:DEFINITION NATP))
 (74 74 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (72 72 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (71 71 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (68 61 (:REWRITE DEFAULT-<-2))
 (67 61 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 24 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (36 36 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (31 31 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (31 7 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (24 24 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (24 24 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (24 24 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (24 24 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (24 24 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (24 24 (:REWRITE DEFAULT-REALPART))
 (24 24 (:REWRITE DEFAULT-NUMERATOR))
 (24 24 (:REWRITE DEFAULT-IMAGPART))
 (24 24 (:REWRITE DEFAULT-DENOMINATOR))
 (24 24 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (16 16 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (14 7 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (12 12 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(RP::RP-EV-FNCALL)
(RP::RP-EXC-ALL
 (803 41 (:DEFINITION APPLY$-BADGEP))
 (490 36 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (479 229 (:REWRITE DEFAULT-+-2))
 (443 389 (:REWRITE DEFAULT-CDR))
 (416 42 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (328 24 (:DEFINITION NATP))
 (306 229 (:REWRITE DEFAULT-+-1))
 (288 18 (:DEFINITION LENGTH))
 (216 18 (:DEFINITION LEN))
 (185 185 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (151 41 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (144 144 (:REWRITE DEFAULT-CAR))
 (144 36 (:DEFINITION INTEGER-ABS))
 (128 36 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (77 65 (:REWRITE DEFAULT-<-2))
 (72 36 (:REWRITE STR::CONSP-OF-EXPLODE))
 (72 36 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (70 70 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (70 65 (:REWRITE DEFAULT-<-1))
 (54 54 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (42 42 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 18 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (18 18 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (18 18 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (18 18 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (18 18 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (15 15 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (10 10 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (6 6 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (5 5 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::RP-EXC-ALL
 (172 1 (:DEFINITION RP::RP-EXC-ALL))
 (134 134 (:REWRITE DEFAULT-CDR))
 (101 5 (:DEFINITION RP::RP-EV-FNCALL))
 (85 85 (:REWRITE DEFAULT-CAR))
 (80 5 (:DEFINITION RP::UNQUOTE-ALL))
 (40 40 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (15 5 (:DEFINITION RP::RP-APPLY-BINDINGS-SUBTERMS))
 (13 13 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (6 2 (:DEFINITION RP::RW-BACKCHAIN-LIMIT))
 (4 2 (:DEFINITION NTH))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (1 1 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 )
(RP::CHECK-SYNP-SYNTAX-AUX)
(RP::RP-RW-RELIEVE-SYNP)
(RP::RP-RW-RELIEVE-SYNP-WRAP)
(RP::REMOVE-RP-FROM-BINDINGS-FOR-SYNP
 (205 6 (:DEFINITION RP::RP-TERMP))
 (80 80 (:REWRITE DEFAULT-CAR))
 (75 75 (:REWRITE DEFAULT-CDR))
 (74 5 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (52 7 (:DEFINITION RP::INCLUDE-FNC-FN))
 (44 15 (:REWRITE RP::RP-TERMP-CADR))
 (38 12 (:REWRITE RP::RP-TERMP-CADDR))
 (37 12 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (24 7 (:DEFINITION QUOTEP))
 (22 22 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (18 7 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (16 4 (:DEFINITION RP::INCLUDE-FNC-SUBTERMS-FN))
 (13 1 (:DEFINITION RP::RP-TERM-LISTP))
 (9 9 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (8 2 (:REWRITE RP::RP-TERMP-CADDDR))
 (7 7 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (4 4 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 )
(RP::RP-RW-META-RULE)
(RP::RP-META-FNC-FORMULA-CHECKS)
(RP::RP-RW-META-RULE-VALID-EVAL)
(RP::RP-RW-META-RULE-VALID-RP-STATEP)
(RP::RP-RW-META-RULE-VALID-RP-TERMP
 (18 18 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (13 3 (:REWRITE RP::RP-TERMP-CADDR))
 (12 3 (:REWRITE RP::RP-TERMP-CADR))
 (8 1 (:DEFINITION RP::RP-TERM-LISTP))
 (6 6 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4 1 (:REWRITE RP::VALID-RP-STATEP-AND-RP-STATEP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 )
(RP::RP-RW-PREPROCESSOR)
(RP::RP-RW-POSTPROCESSOR)
(RP::RP-PROC-FORMULA-CHECKS)
(RP::RP-RW-PREPROCESSOR-VALID-EVAL)
(RP::RP-RW-PREPROCESSOR-VALID-RP-TERMP
 (18 18 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (13 3 (:REWRITE RP::RP-TERMP-CADDR))
 (12 3 (:REWRITE RP::RP-TERMP-CADR))
 (8 1 (:DEFINITION RP::RP-TERM-LISTP))
 (6 6 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4 1 (:REWRITE RP::VALID-RP-STATEP-AND-RP-STATEP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 )
(RP::RP-RW-PREPROCESSOR-RETURNS-VALID-RP-STATEP)
(RP::RP-RW-POSTPROCESSOR-VALID-EVAL)
(RP::RP-RW-POSTPROCESSOR-VALID-RP-TERMP
 (18 18 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (13 3 (:REWRITE RP::RP-TERMP-CADDR))
 (12 3 (:REWRITE RP::RP-TERMP-CADR))
 (8 1 (:DEFINITION RP::RP-TERM-LISTP))
 (6 6 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4 1 (:REWRITE RP::VALID-RP-STATEP-AND-RP-STATEP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 )
(RP::RP-RW-POSTPROCESSOR-RETURNS-VALID-RP-STATEP)
(RP::RP-RW-META-RULE-MAIN)
(RP::RP-RW-META-RULE-INIT)
(RP::RP-META-FNC-FORMULA-CHECKS-INIT)
(RP::RP-RW-PREPROCESSOR-INIT)
(RP::RP-RW-POSTPROCESSOR-INIT)
(RP::RP-PROC-FORMULA-CHECKS-INIT)
(RP::RP-RW-RULE-AUX)
(RP::CHECK-IF-RELIEVED-WITH-RP-AUX
 (69 35 (:REWRITE DEFAULT-+-2))
 (54 48 (:REWRITE DEFAULT-CDR))
 (44 35 (:REWRITE DEFAULT-+-1))
 (37 37 (:REWRITE DEFAULT-CAR))
 (32 2 (:DEFINITION LENGTH))
 (24 2 (:DEFINITION LEN))
 (16 4 (:DEFINITION INTEGER-ABS))
 (12 4 (:DEFINITION APPLY$-BADGEP))
 (10 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (10 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (9 9 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (8 4 (:REWRITE STR::CONSP-OF-EXPLODE))
 (8 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (6 6 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (6 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (2 2 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 )
(RP::CHECK-IF-RELIEVED-WITH-RP)
(RP::RP-RW-FIX-HARD-ERROR-ALIST
 (220 97 (:REWRITE DEFAULT-+-2))
 (130 97 (:REWRITE DEFAULT-+-1))
 (102 90 (:REWRITE DEFAULT-CDR))
 (64 4 (:DEFINITION LENGTH))
 (60 60 (:REWRITE DEFAULT-CAR))
 (48 4 (:DEFINITION LEN))
 (32 8 (:DEFINITION INTEGER-ABS))
 (24 8 (:DEFINITION APPLY$-BADGEP))
 (20 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (20 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (16 8 (:REWRITE STR::CONSP-OF-EXPLODE))
 (16 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (15 10 (:REWRITE DEFAULT-<-2))
 (12 12 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (12 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 4 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (4 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (4 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (4 4 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (4 4 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::RP-RW-FIX-CW-LIST
 (177 97 (:REWRITE DEFAULT-+-2))
 (128 8 (:DEFINITION LENGTH))
 (126 97 (:REWRITE DEFAULT-+-1))
 (96 8 (:DEFINITION LEN))
 (88 64 (:REWRITE DEFAULT-CDR))
 (66 15 (:DEFINITION APPLY$-BADGEP))
 (64 16 (:DEFINITION INTEGER-ABS))
 (61 8 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (51 15 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (40 40 (:REWRITE DEFAULT-CAR))
 (35 7 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (32 16 (:REWRITE STR::CONSP-OF-EXPLODE))
 (24 24 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (20 18 (:REWRITE DEFAULT-<-2))
 (20 18 (:REWRITE DEFAULT-<-1))
 (17 17 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 8 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (15 15 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (15 15 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (10 10 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (8 8 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (8 8 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (8 8 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (8 8 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (8 8 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (5 5 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 )
(RP::TRUE-LISTP-RP-RW-FIX-CW-LIST)
(RP::RP-RW-CHECK-HARD-ERROR-OR-CW)
(RP::DONT-RW-CAR$INLINE)
(RP::DONT-RW-CDR$INLINE)
(RP::MATCH-LHS-FOR-DONT-RW)
(RP::APPLY-BINDINGS-FOR-DONT-RW)
(RP::CALCULATE-DONT-RW$INLINE)
(RP::CALCULATE-DONT-RW-LST$INLINE)
(RP::LIMIT-REACHED-ACTION)
(RP::TRY-TO-UPDATE-BACKCHAINING-RULE)
(RP::POST-BACKCHAIN-OPS)
(RP::CREATE-IF-INSTANCE$INLINE)
(RP::MIN-OF-LIMIT
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 )
(RP::RP-RW-DONT-RW-OR)
(RP::RW-ONLY-WITH-CONTEXT
 (234 120 (:REWRITE DEFAULT-+-2))
 (158 120 (:REWRITE DEFAULT-+-1))
 (128 8 (:DEFINITION LENGTH))
 (114 90 (:REWRITE DEFAULT-CDR))
 (72 62 (:REWRITE DEFAULT-<-1))
 (66 62 (:REWRITE DEFAULT-<-2))
 (64 16 (:REWRITE COMMUTATIVITY-OF-+))
 (64 16 (:DEFINITION INTEGER-ABS))
 (61 61 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (32 16 (:REWRITE STR::CONSP-OF-EXPLODE))
 (27 27 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (26 26 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (24 24 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (24 24 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 8 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (14 14 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (8 8 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (8 8 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (8 8 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (8 8 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::CLEAR-CONTEXT-FOR-RW-ONLY-WITH-CONTEXT)
(RP::RW-ONLY-WITH-CONTEXT-LST$IFF-FLG=T)
(RP::RP-REMOVE-EQUAL)
(RP::END-OF-IF-P)
(RP::CALC-DW-NEGATED-COND-RW$INLINE)
(RP::CALC-CONDS-FOR-RP-RW-IF-1$INLINE
 (124 124 (:TYPE-PRESCRIPTION RP::BINARY-OR**))
 (30 30 (:REWRITE DEFAULT-CDR))
 (24 12 (:DEFINITION NTH))
 (24 6 (:DEFINITION RP::CONS-COUNT-COMPARE-AUX))
 (6 6 (:TYPE-PRESCRIPTION QUOTEP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION RP::IF**))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 )
(RP::RP-RW-RULE
 (1160 8 (:DEFINITION RP::RP-RW-RULE-AUX))
 (1040 863 (:REWRITE DEFAULT-CDR))
 (997 500 (:REWRITE DEFAULT-+-2))
 (976 16 (:DEFINITION RP::RP-MATCH-LHS))
 (688 43 (:DEFINITION LENGTH))
 (666 500 (:REWRITE DEFAULT-+-1))
 (561 561 (:REWRITE DEFAULT-CAR))
 (344 86 (:REWRITE COMMUTATIVITY-OF-+))
 (344 86 (:DEFINITION INTEGER-ABS))
 (322 263 (:REWRITE DEFAULT-<-1))
 (289 263 (:REWRITE DEFAULT-<-2))
 (272 16 (:DEFINITION RP::SHOULD-TERM-BE-IN-CONS$INLINE))
 (235 235 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (183 183 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (172 86 (:REWRITE STR::CONSP-OF-EXPLODE))
 (144 16 (:DEFINITION RP::IS-CONS$INLINE))
 (129 129 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (123 123 (:REWRITE FOLD-CONSTS-IN-+))
 (112 16 (:DEFINITION RP::PUT-TERM-IN-CONS$INLINE))
 (112 16 (:DEFINITION RP::IS-QUOTED-PAIR$INLINE))
 (96 16 (:REWRITE RP::EXTRACT-FROM-RP-WITH-CONTEXT-TO-NO-CONTEXT))
 (86 86 (:REWRITE DEFAULT-UNARY-MINUS))
 (86 43 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (85 85 (:TYPE-PRESCRIPTION LEN))
 (80 16 (:DEFINITION RP::EX-FROM-RP))
 (54 2 (:DEFINITION RP::RW-ONLY-WITH-CONTEXT-LST$IFF-FLG=T))
 (48 16 (:DEFINITION RP::RP-LHS$INLINE))
 (45 45 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (44 2 (:DEFINITION RP::RW-ONLY-WITH-CONTEXT))
 (43 43 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (43 43 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (43 43 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (43 43 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (43 43 (:REWRITE DEFAULT-REALPART))
 (43 43 (:REWRITE DEFAULT-NUMERATOR))
 (43 43 (:REWRITE DEFAULT-IMAGPART))
 (43 43 (:REWRITE DEFAULT-DENOMINATOR))
 (39 39 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (32 8 (:DEFINITION RP::RP-IFF-FLAG$INLINE))
 (26 2 (:DEFINITION RP::CLEAR-CONTEXT-FOR-RW-ONLY-WITH-CONTEXT))
 (18 18 (:REWRITE ZP-OPEN))
 (16 16 (:TYPE-PRESCRIPTION RP::RP-MATCH-LHS-PRECHECK$INLINE))
 (16 16 (:REWRITE RP::EXTRACT-FROM-RP-WITH-CONTEXT-TO-CONTEXT-FROM-RP))
 (16 16 (:DEFINITION ASSOC-EQUAL))
 (16 16 (:DEFINITION ACONS))
 (16 8 (:DEFINITION NTH))
 (10 2 (:DEFINITION RP::INCLUDE-FNC-FN))
 (9 3 (:DEFINITION RP::RP-APPLY-BINDINGS-SUBTERMS))
 (6 6 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (6 2 (:REWRITE AND*-REM-SECOND))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:TYPE-PRESCRIPTION RP::CALCULATE-DONT-RW-LST$INLINE))
 (3 3 (:TYPE-PRESCRIPTION RP::CALC-DW-NEGATED-COND-RW$INLINE))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-EQUALS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-FN))
 (2 2 (:REWRITE AND*-REM-FIRST))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 )
(RP::ATTACH-SC
 (262 262 (:REWRITE RP::MEASURE-LEMMA1))
 (234 94 (:REWRITE RP::MEASURE-LEMMA1-2))
 (168 112 (:REWRITE DEFAULT-CDR))
 (15 15 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (14 14 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 1 (:REWRITE RP::LESS-THAN-IMPLIES-LESS-THAN-OR-EQUAL-TO))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
 (1 1 (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
 (1 1 (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(RP::ATTACH-SC-FROM-CONTEXT)
(RP::ATTACH-SC-FROM-CONTEXT-LST
 (1 1 (:TYPE-PRESCRIPTION RP::ATTACH-SC-FROM-CONTEXT))
 )
(RP::PREPROCESS-THEN-RP-RW)
