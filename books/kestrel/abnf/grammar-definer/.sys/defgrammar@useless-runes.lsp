(ABNF::TRUE-LISTP-OF-SPLIT-///)
(ABNF::ALISTP-WHEN-SYMBOL-ALISTP)
(ABNF::CONSP-OF-CDR-IFF-CDR-WHEN-TRUE-LISTP)
(ABNF::DEFGRAMMAR-ANYP)
(ABNF::BOOLEANP-OF-DEFGRAMMAR-ANYP)
(ABNF::DEFGRAMMAR-ANYP-HOLDS)
(ABNF::DEFGRAMMAR-TABLE-LOOKUP)
(ABNF::BOOLEANP-OF-DEFGRAMMAR-TABLE-LOOKUP)
(ABNF::DEFGRAMMAR-TABLE-ADD)
(ABNF::PSEUDO-EVENT-FORMP-OF-DEFGRAMMAR-TABLE-ADD)
(ABNF::DEFGRAMMAR-PROCESS-NAME
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(ABNF::DEFGRAMMAR-PROCESS-NAME-SYMBOL-WHEN-NOT-ERROR
 (5 5 (:REWRITE RETURN-TYPE-OF-ENSURE-SYMBOL-IS-FRESH-EVENT-NAME.ERP))
 (2 1 (:REWRITE RETURN-TYPE-OF-ENSURE-SYMBOL-IS-FRESH-EVENT-NAME.VAL))
 )
(ABNF::DEFGRAMMAR-PROCESS-INPUTS
 (1394 697 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (333 37 (:DEFINITION ASSOC-EQUAL))
 (200 126 (:REWRITE DEFAULT-CAR))
 (192 16 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (136 8 (:DEFINITION TRUE-LISTP))
 (117 117 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (117 117 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (79 79 (:REWRITE DEFAULT-CDR))
 (48 16 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (32 32 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (32 16 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (32 16 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (32 16 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (32 16 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (16 16 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (16 16 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (16 16 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (16 16 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (16 16 (:REWRITE SET::IN-SET))
 )
(ABNF::RETURN-TYPE-OF-DEFGRAMMAR-PROCESS-INPUTS.VAL
 (18522 2058 (:DEFINITION ASSOC-EQUAL))
 (11154 7038 (:REWRITE DEFAULT-CAR))
 (6940 3470 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (4894 4894 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (4894 4894 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (4864 4856 (:REWRITE DEFAULT-CDR))
 (2400 200 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (1700 100 (:DEFINITION TRUE-LISTP))
 (1024 512 (:REWRITE DEFAULT-+-2))
 (512 512 (:TYPE-PRESCRIPTION LEN))
 (512 512 (:REWRITE DEFAULT-+-1))
 (400 400 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (400 200 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (400 200 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (400 200 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (400 200 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (200 200 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (200 200 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (200 200 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (200 200 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (200 200 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (200 200 (:REWRITE SET::IN-SET))
 )
(ABNF::TRUE-LISTP-OF-DEFGRAMMAR-PROCESS-INPUTS.VAL
 (4954 61 (:REWRITE ABNF::CONSP-OF-CDR-IFF-CDR-WHEN-TRUE-LISTP))
 (3683 138 (:DEFINITION TRUE-LISTP))
 (3560 276 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (2385 265 (:DEFINITION ASSOC-EQUAL))
 (2232 31 (:REWRITE TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (2190 1095 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1416 886 (:REWRITE DEFAULT-CAR))
 (1116 31 (:REWRITE ABNF::TRUE-LISTP-OF-SPLIT-///))
 (829 829 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (829 829 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (631 631 (:REWRITE DEFAULT-CDR))
 (552 552 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (552 276 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (552 276 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (552 276 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (552 276 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (276 276 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (276 276 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (276 276 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (276 276 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (276 276 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (276 276 (:REWRITE SET::IN-SET))
 )
(ABNF::DEFGRAMMAR-GEN-EVERYTHING
 (24 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (17 1 (:DEFINITION TRUE-LISTP))
 (14 2 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (4 4 (:TYPE-PRESCRIPTION STRINGP-OF-IMPLODE))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (4 4 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 (4 2 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (4 2 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE DEFAULT-PKG-IMPORTS))
 (4 2 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (3 1 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (2 2 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (2 2 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE ABNF::TREE-OPTIONP-OF-PARSE-GRAMMAR-FROM-FILE.TREE?))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 )
(ABNF::PSEUDO-EVENT-FORMP-OF-DEFGRAMMAR-GEN-EVERYTHING.EVENT
 (27528 74 (:DEFINITION EXPLODE-ATOM))
 (21608 222 (:DEFINITION EXPLODE-NONNEGATIVE-INTEGER))
 (11544 444 (:DEFINITION FLOOR))
 (8658 222 (:DEFINITION MOD))
 (7992 7992 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (7104 444 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (6882 222 (:DEFINITION DIGIT-TO-CHAR))
 (3226 246 (:DEFINITION BINARY-APPEND))
 (2220 1554 (:REWRITE DEFAULT-+-2))
 (2220 666 (:REWRITE COMMUTATIVITY-OF-*))
 (1752 146 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (1554 1554 (:REWRITE DEFAULT-+-1))
 (1554 1332 (:REWRITE DEFAULT-*-2))
 (1554 1332 (:REWRITE DEFAULT-*-1))
 (1406 1406 (:REWRITE DEFAULT-<-2))
 (1406 1406 (:REWRITE DEFAULT-<-1))
 (1332 444 (:REWRITE COMMUTATIVITY-OF-+))
 (1332 444 (:DEFINITION NFIX))
 (1241 73 (:DEFINITION TRUE-LISTP))
 (1184 444 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (962 740 (:REWRITE DEFAULT-UNARY-MINUS))
 (714 246 (:REWRITE ABNF::CONSP-OF-CDR-IFF-CDR-WHEN-TRUE-LISTP))
 (569 569 (:REWRITE DEFAULT-CDR))
 (565 565 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (565 565 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (518 518 (:REWRITE DEFAULT-NUMERATOR))
 (518 518 (:REWRITE DEFAULT-DENOMINATOR))
 (444 444 (:DEFINITION IFIX))
 (296 148 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (296 148 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (292 292 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (292 146 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (292 146 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (292 146 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (292 146 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (250 250 (:REWRITE DEFAULT-CAR))
 (222 74 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (219 73 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (204 204 (:TYPE-PRESCRIPTION STRINGP-OF-IMPLODE))
 (148 148 (:TYPE-PRESCRIPTION TRUE-LISTP-EXPLODE-NONNEGATIVE-INTEGER))
 (148 148 (:TYPE-PRESCRIPTION EXPLODE-NONNEGATIVE-INTEGER))
 (148 148 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (148 148 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (146 146 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (146 146 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (146 146 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (146 146 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (146 146 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (146 146 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (146 146 (:REWRITE SET::IN-SET))
 (130 74 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (74 74 (:REWRITE ZP-OPEN))
 (74 74 (:REWRITE DEFAULT-SYMBOL-NAME))
 (74 74 (:REWRITE DEFAULT-REALPART))
 (74 74 (:REWRITE DEFAULT-IMAGPART))
 (73 73 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (73 73 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (73 73 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (73 73 (:REWRITE ABNF::TREE-OPTIONP-OF-PARSE-GRAMMAR-FROM-FILE.TREE?))
 (18 18 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 )
(ABNF::DEFGRAMMAR-FN
 (1046 10 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (936 6 (:DEFINITION TRUE-LIST-LISTP))
 (726 10 (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (660 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (631 3 (:DEFINITION SYMBOL-LISTP))
 (601 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (522 16 (:REWRITE ABNF::TRUE-LIST-LISTP-WHEN-TREE-LIST-LISTP))
 (432 36 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (392 18 (:DEFINITION TRUE-LISTP))
 (297 33 (:DEFINITION ASSOC-EQUAL))
 (282 14 (:REWRITE ABNF::TREE-LIST-LISTP-OF-CDR-WHEN-TREE-LIST-LISTP))
 (224 123 (:REWRITE DEFAULT-CAR))
 (191 143 (:REWRITE DEFAULT-CDR))
 (182 30 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-NOT-CONSP))
 (139 139 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (139 139 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (132 33 (:DEFINITION NTH))
 (72 72 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (72 36 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (72 36 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (72 36 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (72 36 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (60 60 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (36 36 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (36 36 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (36 36 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (36 36 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (36 36 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (36 36 (:REWRITE SET::IN-SET))
 (34 4 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (32 16 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (28 2 (:REWRITE SYMBOLP-OF-CAAR-WHEN-SYMBOL-SYMBOL-ALISTP))
 (21 1 (:REWRITE SYMBOL-SYMBOL-ALISTP-OF-CDR-WHEN-SYMBOL-SYMBOL-ALISTP))
 (8 8 (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
 (6 6 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (4 4 (:REWRITE SYMBOL-SYMBOL-ALISTP-WHEN-SUBSETP-EQUAL))
 (4 2 (:REWRITE SYMBOL-SYMBOL-ALISTP-WHEN-NOT-CONSP))
 )
(ABNF::PSEUDO-EVENT-FORMP-OF-DEFGRAMMAR-FN.EVENT
 (166 82 (:REWRITE DEFAULT-CDR))
 (134 24 (:REWRITE DEFAULT-CAR))
 (120 30 (:REWRITE ABNF::CONSP-OF-CDR-IFF-CDR-WHEN-TRUE-LISTP))
 (48 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (34 2 (:DEFINITION TRUE-LISTP))
 (18 2 (:DEFINITION ASSOC-EQUAL))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (8 4 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (8 4 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 2 (:DEFINITION NTH))
 (4 4 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (4 4 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (4 4 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 )
