(NONNIL-SYMBOL-LISTP)
(EQLABLE-LISTP-WHEN-NONNIL-SYMBOL-LISTP
 (15 15 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(INTERP-DEFS-ALISTP)
(HONS-ASSOC-EQUAL-INTERP-DEFS-ALISTP
 (5045 223 (:REWRITE PSEUDO-TERMP-CAR))
 (4630 140 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (3343 93 (:DEFINITION PSEUDO-TERM-LISTP))
 (2804 372 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (1351 354 (:REWRITE PSEUDO-TERMP-OPENER))
 (879 879 (:REWRITE DEFAULT-CDR))
 (874 874 (:REWRITE DEFAULT-CAR))
 (585 117 (:DEFINITION LEN))
 (560 560 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (559 559 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (486 78 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (414 39 (:DEFINITION TRUE-LISTP))
 (278 278 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (234 117 (:REWRITE DEFAULT-+-2))
 (231 39 (:DEFINITION SYMBOL-LISTP))
 (204 12 (:DEFINITION MEMBER-EQUAL))
 (168 24 (:REWRITE SUBSETP-CAR-MEMBER))
 (156 156 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (156 78 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (117 117 (:REWRITE DEFAULT-+-1))
 (102 102 (:REWRITE FN-CHECK-DEF-FORMALS))
 (100 100 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (78 78 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (78 78 (:REWRITE SET::IN-SET))
 (56 56 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (48 48 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (24 24 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (24 24 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (24 24 (:REWRITE SUBSETP-TRANS2))
 (24 24 (:REWRITE SUBSETP-TRANS))
 (24 24 (:REWRITE SUBSETP-MEMBER . 4))
 (24 24 (:REWRITE SUBSETP-MEMBER . 3))
 (24 24 (:REWRITE SUBSETP-MEMBER . 2))
 (24 24 (:REWRITE SUBSETP-MEMBER . 1))
 (24 24 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (24 24 (:REWRITE MEMBER-WHEN-ATOM))
 (24 24 (:REWRITE INTERSECTP-MEMBER . 3))
 (24 24 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(APPLY-FOR-DEFEVALUATOR)
(IFL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(IFL-EV-CONSTRAINT-0)
(IFL-EV-CONSTRAINT-1)
(IFL-EV-CONSTRAINT-2)
(IFL-EV-CONSTRAINT-3)
(IFL-EV-CONSTRAINT-4)
(IFL-EV-CONSTRAINT-5)
(IFL-EV-CONSTRAINT-6)
(IFL-EV-CONSTRAINT-7)
(IFL-EV-CONSTRAINT-8)
(IFL-EV-CONSTRAINT-9)
(IFL-EV-CONSTRAINT-10)
(IFL-EV-CONSTRAINT-11)
(IFL-EV-CONSTRAINT-12)
(IFL-EV-CONSTRAINT-13)
(IFL-EV-CONSTRAINT-14)
(IFL-EV-DISJOIN-CONS)
(IFL-EV-DISJOIN-WHEN-CONSP)
(IFL-EV-DISJOIN-ATOM
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-8))
 )
(IFL-EV-DISJOIN-APPEND
 (23 23 (:REWRITE IFL-EV-CONSTRAINT-8))
 (23 23 (:REWRITE IFL-EV-CONSTRAINT-2))
 )
(IFL-EV-CONJOIN-CONS)
(IFL-EV-CONJOIN-WHEN-CONSP)
(IFL-EV-CONJOIN-ATOM
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-8))
 )
(IFL-EV-CONJOIN-APPEND
 (23 23 (:REWRITE IFL-EV-CONSTRAINT-8))
 (23 23 (:REWRITE IFL-EV-CONSTRAINT-2))
 )
(IFL-EV-CONJOIN-CLAUSES-CONS
 (100 50 (:DEFINITION DISJOIN))
 (50 50 (:DEFINITION DISJOIN2))
 (7 7 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (5 5 (:REWRITE IFL-EV-CONJOIN-ATOM))
 )
(IFL-EV-CONJOIN-CLAUSES-WHEN-CONSP
 (24 24 (:REWRITE IFL-EV-CONSTRAINT-8))
 (24 24 (:REWRITE IFL-EV-CONSTRAINT-2))
 (18 9 (:DEFINITION DISJOIN))
 (9 9 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (9 9 (:DEFINITION DISJOIN2))
 )
(IFL-EV-CONJOIN-CLAUSES-ATOM
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-8))
 )
(IFL-EV-CONJOIN-CLAUSES-APPEND
 (65 65 (:REWRITE IFL-EV-CONSTRAINT-8))
 (65 65 (:REWRITE IFL-EV-CONSTRAINT-2))
 (24 12 (:DEFINITION DISJOIN))
 (12 12 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (12 12 (:DEFINITION DISJOIN2))
 )
(IFL-EV-THEOREMP-CONJOIN-CONS
 (53 53 (:REWRITE IFL-EV-CONJOIN-ATOM))
 )
(IFL-EV-THEOREMP-CONJOIN-APPEND)
(IFL-EV-THEOREMP-CONJOIN-CLAUSES-CONS
 (3 3 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (3 3 (:REWRITE IFL-EV-CONJOIN-ATOM))
 )
(IFL-EV-THEOREMP-CONJOIN-CLAUSES-APPEND
 (15 15 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(IFL-EV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP
 (4 4 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(IFL-EV-THEOREMP-DISJOIN-WHEN-CONSP-UNLESS-THEOREMP
 (4 4 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(IFL-EV-FALSIFY-SUFFICIENT)
(IFL-EV-META-EXTRACT-CONTEXTUAL-BADGUY-SUFFICIENT)
(IFL-EV-META-EXTRACT-GLOBAL-BADGUY-SUFFICIENT)
(IFL-EV-META-EXTRACT-GLOBAL-BADGUY-TRUE-LISTP)
(IFL-EV-META-EXTRACT-TYPESET)
(IFL-EV-META-EXTRACT-RW+-EQUAL)
(IFL-EV-META-EXTRACT-RW+-IFF)
(IFL-EV-META-EXTRACT-RW+-EQUIV)
(IFL-EV-META-EXTRACT-RW-EQUAL)
(IFL-EV-META-EXTRACT-RW-IFF)
(IFL-EV-META-EXTRACT-RW-EQUIV)
(IFL-EV-META-EXTRACT-MFC-AP)
(IFL-EV-META-EXTRACT-RELIEVE-HYP)
(IFL-EV-META-EXTRACT-FORMULA
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-9))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-8))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-3))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-2))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-13))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-12))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-11))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-10))
 (9 9 (:REWRITE IFL-EV-CONSTRAINT-1))
 (8 8 (:REWRITE IFL-EV-CONSTRAINT-7))
 (8 8 (:REWRITE IFL-EV-CONSTRAINT-6))
 )
(IFL-EV-META-EXTRACT-LEMMA-TERM)
(IFL-EV-META-EXTRACT-LEMMA)
(IFL-EV-META-EXTRACT-LINEAR-LEMMA-TERM)
(IFL-EV-META-EXTRACT-LINEAR-LEMMA)
(IFL-EV-META-EXTRACT-FNCALL-LOGIC)
(IFL-EV-META-EXTRACT-FNCALL)
(IFL-EV-META-EXTRACT-MAGIC-EV)
(IFL-EV-META-EXTRACT-MAGIC-EV-LST)
(IFL-EV-META-EXTRACT-FN-CHECK-DEF)
(IFL-EV-LST-OF-PAIRLIS)
(IFL-EV-LST-OF-PAIRLIS-APPEND-REST)
(IFL-EV-LST-OF-PAIRLIS-APPEND-HEAD-REST)
(META-EXTRACT-FUNCTION-FORMALS/BODY)
(IFL-EV-META-EXTRACT-FUNCTION-FORMALS/BODY
 (4604 80 (:DEFINITION PSEUDO-TERM-LISTP))
 (4152 48 (:DEFINITION PSEUDO-TERMP))
 (4126 130 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (3904 302 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (3204 302 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (2574 138 (:REWRITE PSEUDO-TERMP-CAR))
 (1828 258 (:REWRITE PSEUDO-TERMP-OPENER))
 (1184 1184 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (916 871 (:REWRITE DEFAULT-CAR))
 (851 851 (:REWRITE DEFAULT-CDR))
 (610 110 (:DEFINITION LEN))
 (520 10 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (470 470 (:TYPE-PRESCRIPTION LEN))
 (388 388 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (388 388 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (360 60 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (280 20 (:REWRITE SUBSETP-CAR-MEMBER))
 (250 38 (:DEFINITION TRUE-LISTP))
 (240 10 (:DEFINITION MEMBER-EQUAL))
 (228 114 (:REWRITE DEFAULT-+-2))
 (212 212 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (172 28 (:DEFINITION SYMBOL-LISTP))
 (145 145 (:TYPE-PRESCRIPTION KWOTE-LST))
 (140 20 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (120 120 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (120 60 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (114 114 (:REWRITE DEFAULT-+-1))
 (108 108 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (104 71 (:REWRITE IFL-EV-CONSTRAINT-14))
 (104 71 (:REWRITE IFL-EV-CONSTRAINT-13))
 (104 71 (:REWRITE IFL-EV-CONSTRAINT-12))
 (104 71 (:REWRITE IFL-EV-CONSTRAINT-11))
 (104 71 (:REWRITE IFL-EV-CONSTRAINT-10))
 (96 63 (:REWRITE IFL-EV-CONSTRAINT-8))
 (96 63 (:REWRITE IFL-EV-CONSTRAINT-3))
 (80 80 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (76 76 (:REWRITE FN-CHECK-DEF-FORMALS))
 (62 57 (:REWRITE IFL-EV-CONSTRAINT-1))
 (60 60 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (60 60 (:REWRITE SET::IN-SET))
 (56 56 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (40 40 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (40 40 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (40 40 (:REWRITE SUBSETP-TRANS2))
 (40 40 (:REWRITE SUBSETP-TRANS))
 (40 10 (:DEFINITION NONNIL-SYMBOL-LISTP))
 (28 28 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (20 20 (:REWRITE SUBSETP-MEMBER . 4))
 (20 20 (:REWRITE SUBSETP-MEMBER . 3))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (20 20 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (20 20 (:REWRITE MEMBER-WHEN-ATOM))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 3))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 2))
 (20 5 (:DEFINITION KWOTE-LST))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (5 5 (:REWRITE IFL-EV-CONSTRAINT-5))
 (5 5 (:REWRITE IFL-EV-CONSTRAINT-4))
 (5 5 (:DEFINITION KWOTE))
 )
(META-EXTRACT-FUNCTION-FORMALS/BODY-WELL-FORMED
 (1629 20 (:DEFINITION PSEUDO-TERM-LISTP))
 (1558 12 (:DEFINITION PSEUDO-TERMP))
 (1416 39 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (1326 88 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (1111 88 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (857 41 (:REWRITE PSEUDO-TERMP-CAR))
 (628 77 (:REWRITE PSEUDO-TERMP-OPENER))
 (354 354 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (270 270 (:REWRITE DEFAULT-CDR))
 (256 256 (:REWRITE DEFAULT-CAR))
 (224 40 (:DEFINITION LEN))
 (202 202 (:TYPE-PRESCRIPTION LEN))
 (156 3 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (120 20 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (114 114 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (114 114 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (90 12 (:DEFINITION TRUE-LISTP))
 (88 44 (:REWRITE DEFAULT-+-2))
 (84 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (78 12 (:DEFINITION SYMBOL-LISTP))
 (72 3 (:DEFINITION MEMBER-EQUAL))
 (63 63 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (52 52 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (44 44 (:REWRITE DEFAULT-+-1))
 (42 6 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (40 40 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (40 20 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (30 30 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (20 20 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (20 20 (:REWRITE SET::IN-SET))
 (12 12 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (12 12 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (12 12 (:REWRITE SUBSETP-TRANS2))
 (12 12 (:REWRITE SUBSETP-TRANS))
 (12 3 (:DEFINITION NONNIL-SYMBOL-LISTP))
 (7 7 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (6 6 (:REWRITE SUBSETP-MEMBER . 4))
 (6 6 (:REWRITE SUBSETP-MEMBER . 3))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (6 6 (:REWRITE MEMBER-WHEN-ATOM))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 2))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(INTERP-FUNCTION-LOOKUP
 (70 66 (:REWRITE DEFAULT-CAR))
 (40 36 (:REWRITE DEFAULT-CDR))
 )
(INTERP-FUNCTION-LOOKUP-DEFS-ALISTP
 (18033 776 (:REWRITE PSEUDO-TERMP-CAR))
 (17518 464 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (14875 279 (:DEFINITION PSEUDO-TERM-LISTP))
 (10671 1202 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (6892 3422 (:REWRITE DEFAULT-CDR))
 (6816 3298 (:REWRITE DEFAULT-CAR))
 (5246 1130 (:REWRITE PSEUDO-TERMP-OPENER))
 (4530 396 (:DEFINITION LEN))
 (1781 1781 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (1780 1780 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1520 248 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (1480 77 (:DEFINITION MEMBER-EQUAL))
 (1437 124 (:DEFINITION TRUE-LISTP))
 (1078 154 (:REWRITE SUBSETP-CAR-MEMBER))
 (879 879 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (846 423 (:REWRITE DEFAULT-+-2))
 (823 127 (:DEFINITION SYMBOL-LISTP))
 (496 496 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (496 248 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (423 423 (:REWRITE DEFAULT-+-1))
 (408 408 (:REWRITE FN-CHECK-DEF-FORMALS))
 (384 384 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (308 308 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (248 248 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (248 248 (:REWRITE SET::IN-SET))
 (206 206 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (154 154 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (154 154 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (154 154 (:REWRITE SUBSETP-TRANS2))
 (154 154 (:REWRITE SUBSETP-TRANS))
 (154 154 (:REWRITE SUBSETP-MEMBER . 4))
 (154 154 (:REWRITE SUBSETP-MEMBER . 3))
 (154 154 (:REWRITE SUBSETP-MEMBER . 2))
 (154 154 (:REWRITE SUBSETP-MEMBER . 1))
 (154 154 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (154 154 (:REWRITE MEMBER-WHEN-ATOM))
 (154 154 (:REWRITE INTERSECTP-MEMBER . 3))
 (154 154 (:REWRITE INTERSECTP-MEMBER . 2))
 (24 6 (:REWRITE FOLD-CONSTS-IN-+))
 )
(INTERP-FUNCTION-LOOKUP-DEFS-ALISTP-MEANS-IN-DEFS-ALISTP
 (4180 188 (:REWRITE PSEUDO-TERMP-CAR))
 (3737 123 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (3131 74 (:DEFINITION PSEUDO-TERM-LISTP))
 (2449 297 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (1438 1438 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1006 1006 (:REWRITE DEFAULT-CAR))
 (972 311 (:REWRITE PSEUDO-TERMP-OPENER))
 (918 918 (:REWRITE DEFAULT-CDR))
 (699 124 (:DEFINITION LEN))
 (453 453 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (452 452 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (448 68 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (385 34 (:DEFINITION TRUE-LISTP))
 (263 263 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (256 128 (:REWRITE DEFAULT-+-2))
 (241 40 (:DEFINITION SYMBOL-LISTP))
 (221 13 (:DEFINITION MEMBER-EQUAL))
 (182 26 (:REWRITE SUBSETP-CAR-MEMBER))
 (136 136 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (136 68 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (128 128 (:REWRITE DEFAULT-+-1))
 (106 106 (:REWRITE FN-CHECK-DEF-FORMALS))
 (84 84 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (68 68 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (68 68 (:REWRITE SET::IN-SET))
 (52 52 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (42 42 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (26 26 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (26 26 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (26 26 (:REWRITE SUBSETP-TRANS2))
 (26 26 (:REWRITE SUBSETP-TRANS))
 (26 26 (:REWRITE SUBSETP-MEMBER . 4))
 (26 26 (:REWRITE SUBSETP-MEMBER . 3))
 (26 26 (:REWRITE SUBSETP-MEMBER . 2))
 (26 26 (:REWRITE SUBSETP-MEMBER . 1))
 (26 26 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (26 26 (:REWRITE MEMBER-WHEN-ATOM))
 (26 26 (:REWRITE INTERSECTP-MEMBER . 3))
 (26 26 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(INTERP-FUNCTION-LOOKUP-WFP
 (1758 12 (:DEFINITION PSEUDO-TERMP))
 (1546 76 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (1120 40 (:REWRITE PSEUDO-TERMP-CAR))
 (1118 32 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (548 76 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (532 16 (:DEFINITION PSEUDO-TERM-LISTP))
 (368 368 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (368 350 (:REWRITE DEFAULT-CAR))
 (295 283 (:REWRITE DEFAULT-CDR))
 (270 38 (:DEFINITION LEN))
 (176 176 (:TYPE-PRESCRIPTION LEN))
 (168 24 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (160 84 (:REWRITE PSEUDO-TERMP-OPENER))
 (158 78 (:REWRITE HONS-ASSOC-EQUAL-INTERP-DEFS-ALISTP))
 (156 12 (:DEFINITION TRUE-LISTP))
 (152 4 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (116 116 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (116 116 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (80 80 (:TYPE-PRESCRIPTION INTERP-DEFS-ALISTP))
 (80 80 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (80 40 (:REWRITE DEFAULT-+-2))
 (72 12 (:DEFINITION SYMBOL-LISTP))
 (68 4 (:DEFINITION MEMBER-EQUAL))
 (56 8 (:REWRITE SUBSETP-CAR-MEMBER))
 (48 48 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (48 24 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (44 44 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (40 40 (:REWRITE DEFAULT-+-1))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 24 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (24 24 (:REWRITE SET::IN-SET))
 (16 16 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (16 4 (:DEFINITION NONNIL-SYMBOL-LISTP))
 (12 12 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (8 8 (:REWRITE SUBSETP-TRANS2))
 (8 8 (:REWRITE SUBSETP-TRANS))
 (8 8 (:REWRITE SUBSETP-MEMBER . 4))
 (8 8 (:REWRITE SUBSETP-MEMBER . 3))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (8 8 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (8 8 (:REWRITE MEMBER-WHEN-ATOM))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 3))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 2))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(INTERP-DEFS-ALIST-CLAUSES
 (322 24 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (307 2 (:DEFINITION PSEUDO-TERMP))
 (298 15 (:REWRITE PSEUDO-TERMP-CAR))
 (210 8 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (173 6 (:DEFINITION PSEUDO-TERM-LISTP))
 (152 24 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (113 113 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (100 22 (:REWRITE PSEUDO-TERMP-OPENER))
 (55 55 (:REWRITE DEFAULT-CDR))
 (49 49 (:REWRITE DEFAULT-CAR))
 (38 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (37 37 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (37 37 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (30 6 (:DEFINITION LEN))
 (25 25 (:TYPE-PRESCRIPTION LEN))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (19 2 (:DEFINITION TRUE-LISTP))
 (17 1 (:DEFINITION MEMBER-EQUAL))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (14 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (12 6 (:REWRITE DEFAULT-+-2))
 (11 2 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 1 (:DEFINITION NONNIL-SYMBOL-LISTP))
 (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 4))
 (2 2 (:REWRITE SUBSETP-MEMBER . 3))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (2 2 (:REWRITE MEMBER-WHEN-ATOM))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 3))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 2))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(IFL-EV-THEOREMP-CONJUNCTS
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-9))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-8))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-3))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-2))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-14))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-13))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-12))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-11))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-10))
 (73 73 (:REWRITE IFL-EV-CONSTRAINT-1))
 (38 38 (:REWRITE IFL-EV-CONJOIN-ATOM))
 )
(IFL-EV-THEOREMP-REMOVE-FIRST-LIT-WHEN-FALSE
 (60 44 (:REWRITE IFL-EV-CONSTRAINT-14))
 (60 44 (:REWRITE IFL-EV-CONSTRAINT-13))
 (60 44 (:REWRITE IFL-EV-CONSTRAINT-12))
 (60 44 (:REWRITE IFL-EV-CONSTRAINT-11))
 (52 52 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE IFL-EV-CONSTRAINT-9))
 (34 34 (:REWRITE IFL-EV-CONSTRAINT-8))
 (34 34 (:REWRITE IFL-EV-CONSTRAINT-3))
 (34 34 (:REWRITE IFL-EV-CONSTRAINT-2))
 (34 34 (:REWRITE IFL-EV-CONSTRAINT-1))
 (20 20 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (10 10 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(IFL-EV-OF-DISJOIN-APPEND
 (6 6 (:REWRITE IFL-EV-DISJOIN-ATOM))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-9))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-8))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-3))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-2))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-14))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-13))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-12))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-11))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-10))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-1))
 (4 1 (:DEFINITION BINARY-APPEND))
 (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(IFL-EV-THEOREMP-OF-CONJOIN-CLAUSES-CONS
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-9))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-8))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-3))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-2))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-14))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-13))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-12))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-11))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-10))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-1))
 (6 3 (:REWRITE IFL-EV-CONJOIN-ATOM))
 (3 3 (:TYPE-PRESCRIPTION DISJOIN-LST))
 (3 3 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(IFL-EV-THEOREMP-OF-CONJOIN-CLAUSES-APPEND
 (8 2 (:DEFINITION BINARY-APPEND))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-9))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-8))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-3))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-2))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-14))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-13))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-12))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-11))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-10))
 (6 6 (:REWRITE IFL-EV-CONSTRAINT-1))
 (6 6 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (4 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(HONS-ASSOC-EQUAL-IFL-EV-DEFS-ALIST-EQUALITY
 (190 96 (:REWRITE IFL-EV-CONSTRAINT-13))
 (190 96 (:REWRITE IFL-EV-CONSTRAINT-12))
 (190 96 (:REWRITE IFL-EV-CONSTRAINT-11))
 (114 64 (:REWRITE IFL-EV-CONSTRAINT-3))
 (68 68 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (24 12 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (12 12 (:TYPE-PRESCRIPTION INTERP-DEFS-ALIST-CLAUSES))
 (6 6 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY
 (2473 19 (:DEFINITION PSEUDO-TERMP))
 (2041 105 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (1706 50 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (1618 62 (:REWRITE PSEUDO-TERMP-CAR))
 (1245 24 (:DEFINITION PSEUDO-TERM-LISTP))
 (994 105 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (635 635 (:REWRITE DEFAULT-CAR))
 (520 520 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (506 506 (:REWRITE DEFAULT-CDR))
 (366 60 (:DEFINITION LEN))
 (293 293 (:TYPE-PRESCRIPTION LEN))
 (224 32 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (216 123 (:REWRITE PSEUDO-TERMP-OPENER))
 (204 16 (:DEFINITION TRUE-LISTP))
 (190 5 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (159 159 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (159 159 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (126 63 (:REWRITE DEFAULT-+-2))
 (118 118 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (118 19 (:DEFINITION SYMBOL-LISTP))
 (85 5 (:DEFINITION MEMBER-EQUAL))
 (83 1 (:REWRITE IFL-EV-THEOREMP-REMOVE-FIRST-LIT-WHEN-FALSE))
 (78 12 (:REWRITE IFL-EV-CONSTRAINT-10))
 (75 75 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (70 10 (:REWRITE SUBSETP-CAR-MEMBER))
 (64 64 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (64 32 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (63 63 (:REWRITE DEFAULT-+-1))
 (54 13 (:REWRITE IFL-EV-CONSTRAINT-14))
 (48 48 (:REWRITE FN-CHECK-DEF-FORMALS))
 (44 44 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (32 32 (:REWRITE SET::IN-SET))
 (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (20 5 (:DEFINITION NONNIL-SYMBOL-LISTP))
 (18 12 (:REWRITE IFL-EV-CONSTRAINT-13))
 (18 12 (:REWRITE IFL-EV-CONSTRAINT-12))
 (18 12 (:REWRITE IFL-EV-CONSTRAINT-11))
 (16 16 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (12 10 (:REWRITE IFL-EV-CONSTRAINT-9))
 (12 10 (:REWRITE IFL-EV-CONSTRAINT-8))
 (12 10 (:REWRITE IFL-EV-CONSTRAINT-3))
 (10 10 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (10 10 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (10 10 (:REWRITE SUBSETP-TRANS2))
 (10 10 (:REWRITE SUBSETP-TRANS))
 (10 10 (:REWRITE SUBSETP-MEMBER . 4))
 (10 10 (:REWRITE SUBSETP-MEMBER . 3))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (10 10 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (10 10 (:REWRITE MEMBER-WHEN-ATOM))
 (10 10 (:REWRITE INTERSECTP-MEMBER . 3))
 (10 10 (:REWRITE INTERSECTP-MEMBER . 2))
 (10 10 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 2 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (3 3 (:REWRITE IFL-EV-CONSTRAINT-1))
 (2 2 (:TYPE-PRESCRIPTION INTERP-DEFS-ALIST-CLAUSES))
 (1 1 (:REWRITE IFL-EV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP))
 (1 1 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(INTERP-FUNCTION-LOOKUP-CORRECT-1
 (3568 120 (:DEFINITION PSEUDO-TERM-LISTP))
 (2632 122 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (2494 160 (:REWRITE PSEUDO-TERMP-CAR))
 (2106 218 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (1074 1074 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1024 218 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (496 248 (:REWRITE HONS-ASSOC-EQUAL-INTERP-DEFS-ALISTP))
 (450 30 (:DEFINITION MEMBER-EQUAL))
 (420 60 (:REWRITE SUBSETP-CAR-MEMBER))
 (378 356 (:REWRITE PSEUDO-TERMP-OPENER))
 (356 356 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (322 322 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (322 322 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (248 248 (:TYPE-PRESCRIPTION INTERP-DEFS-ALISTP))
 (229 144 (:REWRITE IFL-EV-CONSTRAINT-13))
 (229 144 (:REWRITE IFL-EV-CONSTRAINT-12))
 (229 144 (:REWRITE IFL-EV-CONSTRAINT-11))
 (159 106 (:REWRITE IFL-EV-CONSTRAINT-8))
 (159 106 (:REWRITE IFL-EV-CONSTRAINT-3))
 (120 120 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (77 77 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (60 60 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (60 60 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (60 60 (:REWRITE SUBSETP-TRANS2))
 (60 60 (:REWRITE SUBSETP-TRANS))
 (60 60 (:REWRITE SUBSETP-MEMBER . 4))
 (60 60 (:REWRITE SUBSETP-MEMBER . 3))
 (60 60 (:REWRITE SUBSETP-MEMBER . 2))
 (60 60 (:REWRITE SUBSETP-MEMBER . 1))
 (60 60 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (60 60 (:REWRITE MEMBER-WHEN-ATOM))
 (60 60 (:REWRITE INTERSECTP-MEMBER . 3))
 (60 60 (:REWRITE INTERSECTP-MEMBER . 2))
 (60 60 (:REWRITE FN-CHECK-DEF-FORMALS))
 (26 13 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (13 13 (:TYPE-PRESCRIPTION INTERP-DEFS-ALIST-CLAUSES))
 (13 13 (:REWRITE INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY))
 (10 10 (:REWRITE IFL-EV-DISJOIN-ATOM))
 )
(IFL-EV-LST-ACONS-NON-MEMBER
 (32 32 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE SUBSETP-MEMBER . 4))
 (7 7 (:REWRITE SUBSETP-MEMBER . 3))
 (7 7 (:REWRITE SUBSETP-MEMBER . 2))
 (7 7 (:REWRITE INTERSECTP-MEMBER . 3))
 (7 7 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-9))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-8))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-3))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-2))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-14))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-13))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-12))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-11))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-10))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 )
(IFL-EV-LST-PAIRLIS
 (277 12 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (201 11 (:DEFINITION MEMBER-EQUAL))
 (192 24 (:REWRITE SUBSETP-CAR-MEMBER))
 (174 16 (:DEFINITION TRUE-LISTP))
 (166 31 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (107 107 (:REWRITE DEFAULT-CDR))
 (80 76 (:REWRITE DEFAULT-CAR))
 (69 7 (:REWRITE IFL-EV-LST-OF-PAIRLIS))
 (67 34 (:REWRITE DEFAULT-+-2))
 (64 64 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (54 54 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (54 54 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (54 27 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (42 6 (:DEFINITION SYMBOL-LISTP))
 (34 34 (:REWRITE DEFAULT-+-1))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (28 28 (:REWRITE SUBSETP-TRANS2))
 (28 28 (:REWRITE SUBSETP-TRANS))
 (28 4 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (27 27 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (27 27 (:REWRITE SET::IN-SET))
 (26 26 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (26 26 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (24 24 (:REWRITE FN-CHECK-DEF-FORMALS))
 (22 22 (:REWRITE SUBSETP-MEMBER . 4))
 (22 22 (:REWRITE SUBSETP-MEMBER . 3))
 (22 22 (:REWRITE SUBSETP-MEMBER . 2))
 (22 22 (:REWRITE SUBSETP-MEMBER . 1))
 (22 22 (:REWRITE MEMBER-WHEN-ATOM))
 (22 22 (:REWRITE INTERSECTP-MEMBER . 3))
 (22 22 (:REWRITE INTERSECTP-MEMBER . 2))
 (12 12 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (11 11 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-REFL))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-9))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-8))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-3))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-2))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-14))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-13))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-12))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-11))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-10))
 )
(KWOTE-LIST-LIST-FIX
 (186 9 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (114 19 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (107 10 (:DEFINITION TRUE-LISTP))
 (43 43 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (38 38 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (38 19 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (27 27 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-+-2))
 (19 19 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (19 19 (:REWRITE SET::IN-SET))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-CAR))
 )
(IFL-EV-CONS-PAIRLIS
 (32 23 (:REWRITE DEFAULT-CAR))
 (20 1 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (11 1 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (11 1 (:DEFINITION TRUE-LISTP))
 (10 2 (:DEFINITION PAIRLIS$))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-9))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-8))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-3))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-2))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-14))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-13))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-12))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-11))
 (9 2 (:REWRITE IFL-EV-CONSTRAINT-10))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 1 (:DEFINITION LEN))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 1 (:DEFINITION KWOTE-LST))
 (3 2 (:REWRITE IFL-EV-CONSTRAINT-1))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:DEFINITION KWOTE))
 )
(INTERP-FUNCTION-LOOKUP-CORRECT-2
 (36 27 (:REWRITE DEFAULT-CAR))
 (30 2 (:DEFINITION INTERP-DEFS-ALIST-CLAUSES))
 (20 20 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (9 9 (:REWRITE CAR-CONS))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-9))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-8))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-3))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-2))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-14))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-13))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-12))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-11))
 (9 4 (:REWRITE IFL-EV-CONSTRAINT-10))
 (8 2 (:DEFINITION KWOTE-LST))
 (6 4 (:REWRITE IFL-EV-CONSTRAINT-1))
 (5 1 (:DEFINITION PAIRLIS$))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:DEFINITION KWOTE))
 (2 1 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (1 1 (:TYPE-PRESCRIPTION INTERP-DEFS-ALIST-CLAUSES))
 (1 1 (:REWRITE INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY))
 (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(LEN-IFL-EV-LST
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-9))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-8))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-3))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-2))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-14))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-13))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-12))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-11))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-10))
 (1 1 (:REWRITE IFL-EV-CONSTRAINT-1))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(INTERP-FUNCTION-LOOKUP-CORRECT
 (47 38 (:REWRITE DEFAULT-CAR))
 (30 30 (:TYPE-PRESCRIPTION KWOTE-LST))
 (30 2 (:DEFINITION INTERP-DEFS-ALIST-CLAUSES))
 (23 23 (:REWRITE DEFAULT-CDR))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-9))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-8))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-3))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-2))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-14))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-13))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-12))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-11))
 (12 5 (:REWRITE IFL-EV-CONSTRAINT-10))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 2 (:DEFINITION KWOTE-LST))
 (7 5 (:REWRITE IFL-EV-CONSTRAINT-1))
 (5 1 (:DEFINITION PAIRLIS$))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE IFL-EV-META-EXTRACT-FN-CHECK-DEF))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-5))
 (2 2 (:REWRITE IFL-EV-CONSTRAINT-4))
 (2 2 (:DEFINITION KWOTE))
 (2 1 (:REWRITE IFL-EV-CONJOIN-CLAUSES-ATOM))
 (1 1 (:TYPE-PRESCRIPTION INTERP-DEFS-ALIST-CLAUSES))
 (1 1 (:REWRITE INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY))
 (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(APPLY-FOR-DEFEVALUATOR)
(FOO-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(FOO-EV-CONSTRAINT-0)
(FOO-EV-CONSTRAINT-1)
(FOO-EV-CONSTRAINT-2)
(FOO-EV-CONSTRAINT-3)
(FOO-EV-CONSTRAINT-4)
(FOO-EV-CONSTRAINT-5)
(FOO-EV-CONSTRAINT-6)
(FOO-EV-CONSTRAINT-7)
(FOO-EV-CONSTRAINT-8)
(FOO-EV-CONSTRAINT-9)
(FOO-EV-CONSTRAINT-10)
(FOO-EV-CONSTRAINT-11)
(FOO-EV-CONSTRAINT-12)
(FOO-EV-CONSTRAINT-13)
(FOO-EV-CONSTRAINT-14)
(FOO-EV-CONSTRAINT-15)
(FOO-EV-CONSTRAINT-16)
(FOO-EV-CONSTRAINT-17)
(FOO-EV-CONSTRAINT-18)
(FOO-EV-CONSTRAINT-19)
(FOO-EV-CONSTRAINT-20)
(FOO-EV-CONSTRAINT-21)
(FOO-EV-DISJOIN-CONS)
(FOO-EV-DISJOIN-WHEN-CONSP)
(FOO-EV-DISJOIN-ATOM
 (1 1 (:REWRITE FOO-EV-CONSTRAINT-8))
 )
(FOO-EV-DISJOIN-APPEND
 (23 23 (:REWRITE FOO-EV-CONSTRAINT-8))
 (23 23 (:REWRITE FOO-EV-CONSTRAINT-2))
 )
(FOO-EV-CONJOIN-CONS)
(FOO-EV-CONJOIN-WHEN-CONSP)
(FOO-EV-CONJOIN-ATOM
 (1 1 (:REWRITE FOO-EV-CONSTRAINT-8))
 )
(FOO-EV-CONJOIN-APPEND
 (23 23 (:REWRITE FOO-EV-CONSTRAINT-8))
 (23 23 (:REWRITE FOO-EV-CONSTRAINT-2))
 )
(FOO-EV-CONJOIN-CLAUSES-CONS
 (100 50 (:DEFINITION DISJOIN))
 (50 50 (:DEFINITION DISJOIN2))
 (7 7 (:REWRITE FOO-EV-DISJOIN-ATOM))
 (5 5 (:REWRITE FOO-EV-CONJOIN-ATOM))
 )
(FOO-EV-CONJOIN-CLAUSES-WHEN-CONSP
 (24 24 (:REWRITE FOO-EV-CONSTRAINT-8))
 (24 24 (:REWRITE FOO-EV-CONSTRAINT-2))
 (18 9 (:DEFINITION DISJOIN))
 (9 9 (:REWRITE FOO-EV-DISJOIN-ATOM))
 (9 9 (:DEFINITION DISJOIN2))
 )
(FOO-EV-CONJOIN-CLAUSES-ATOM
 (1 1 (:REWRITE FOO-EV-CONSTRAINT-8))
 )
(FOO-EV-CONJOIN-CLAUSES-APPEND
 (65 65 (:REWRITE FOO-EV-CONSTRAINT-8))
 (65 65 (:REWRITE FOO-EV-CONSTRAINT-2))
 (24 12 (:DEFINITION DISJOIN))
 (12 12 (:REWRITE FOO-EV-DISJOIN-ATOM))
 (12 12 (:DEFINITION DISJOIN2))
 )
(FOO-EV-THEOREMP-CONJOIN-CONS
 (53 53 (:REWRITE FOO-EV-CONJOIN-ATOM))
 )
(FOO-EV-THEOREMP-CONJOIN-APPEND)
(FOO-EV-THEOREMP-CONJOIN-CLAUSES-CONS
 (3 3 (:REWRITE FOO-EV-DISJOIN-ATOM))
 (3 3 (:REWRITE FOO-EV-CONJOIN-ATOM))
 )
(FOO-EV-THEOREMP-CONJOIN-CLAUSES-APPEND
 (15 15 (:REWRITE FOO-EV-DISJOIN-ATOM))
 )
(FOO-EV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP
 (4 4 (:REWRITE FOO-EV-DISJOIN-ATOM))
 )
(FOO-EV-THEOREMP-DISJOIN-WHEN-CONSP-UNLESS-THEOREMP
 (4 4 (:REWRITE FOO-EV-DISJOIN-ATOM))
 )
(FOO-EV-FALSIFY-SUFFICIENT)
(FOO-EV-META-EXTRACT-CONTEXTUAL-BADGUY-SUFFICIENT)
(FOO-EV-META-EXTRACT-GLOBAL-BADGUY-SUFFICIENT)
(FOO-EV-META-EXTRACT-GLOBAL-BADGUY-TRUE-LISTP)
(FOO-EV-META-EXTRACT-TYPESET)
(FOO-EV-META-EXTRACT-RW+-EQUAL)
(FOO-EV-META-EXTRACT-RW+-IFF)
(FOO-EV-META-EXTRACT-RW+-EQUIV)
(FOO-EV-META-EXTRACT-RW-EQUAL)
(FOO-EV-META-EXTRACT-RW-IFF)
(FOO-EV-META-EXTRACT-RW-EQUIV)
(FOO-EV-META-EXTRACT-MFC-AP)
(FOO-EV-META-EXTRACT-RELIEVE-HYP)
(FOO-EV-META-EXTRACT-FORMULA
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-9))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-8))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-3))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-2))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-14))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-13))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-12))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-10))
 (9 9 (:REWRITE FOO-EV-CONSTRAINT-1))
 (8 8 (:REWRITE FOO-EV-CONSTRAINT-7))
 (8 8 (:REWRITE FOO-EV-CONSTRAINT-6))
 )
(FOO-EV-META-EXTRACT-LEMMA-TERM)
(FOO-EV-META-EXTRACT-LEMMA)
(FOO-EV-META-EXTRACT-LINEAR-LEMMA-TERM)
(FOO-EV-META-EXTRACT-LINEAR-LEMMA)
(FOO-EV-META-EXTRACT-FNCALL-LOGIC)
(FOO-EV-META-EXTRACT-FNCALL)
(FOO-EV-META-EXTRACT-MAGIC-EV)
(FOO-EV-META-EXTRACT-MAGIC-EV-LST)
(FOO-EV-META-EXTRACT-FN-CHECK-DEF)
(FOO-EV-LST-OF-PAIRLIS)
(FOO-EV-LST-OF-PAIRLIS-APPEND-REST)
(FOO-EV-LST-OF-PAIRLIS-APPEND-HEAD-REST)
(INTERP-FUNCTION-LOOKUP-CORRECT-FOR-FOO-EV
 (246 2 (:DEFINITION BINARY-LOGAND))
 (228 164 (:REWRITE DEFAULT-CAR))
 (156 4 (:DEFINITION FLOOR))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-21))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-20))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-19))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-18))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-17))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-16))
 (107 85 (:REWRITE FOO-EV-CONSTRAINT-15))
 (96 6 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (72 72 (:REWRITE DEFAULT-CDR))
 (64 64 (:REWRITE CAR-CONS))
 (62 14 (:REWRITE COMMUTATIVITY-OF-+))
 (48 34 (:REWRITE DEFAULT-+-2))
 (42 34 (:REWRITE DEFAULT-+-1))
 (24 22 (:REWRITE DEFAULT-<-1))
 (24 8 (:REWRITE COMMUTATIVITY-OF-*))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (24 4 (:DEFINITION EVENP))
 (22 22 (:REWRITE DEFAULT-<-2))
 (20 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (18 6 (:DEFINITION NFIX))
 (16 4 (:DEFINITION KWOTE-LST))
 (16 2 (:DEFINITION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (12 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:REWRITE UNICITY-OF-0))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 8 (:REWRITE FOO-EV-CONSTRAINT-4))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 4 (:DEFINITION FIX))
 (6 6 (:DEFINITION IFIX))
 (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE FOO-EV-META-EXTRACT-FN-CHECK-DEF))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:DEFINITION KWOTE))
 (4 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INTERP-FUNCTION-LOOKUP-CORRECT-2-FOR-FOO-EV)
(INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY-FOR-FOO-EV)
(FOO-EV-THEOREMP-OF-CONJOIN-CLAUSES-CONS)
(FOO-EV-THEOREMP-OF-CONJOIN-CLAUSES-APPEND)
