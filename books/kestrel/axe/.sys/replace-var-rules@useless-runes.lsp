(DARGP-OF-MAYBE-REPLACE-VAR
 (1145 295 (:REWRITE DEFAULT-CAR))
 (970 161 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (844 30 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (700 203 (:REWRITE DEFAULT-CDR))
 (585 1 (:DEFINITION AXE-TREEP))
 (484 2 (:DEFINITION PSEUDO-TERMP))
 (391 158 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (322 161 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (316 316 (:TYPE-PRESCRIPTION ALL-CONSP))
 (275 275 (:REWRITE USE-ALL-CONSP-2))
 (275 275 (:REWRITE USE-ALL-CONSP))
 (219 24 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (205 10 (:DEFINITION LEN))
 (199 1 (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP))
 (161 161 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (161 3 (:DEFINITION SYMBOL-LISTP))
 (158 158 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (69 8 (:REWRITE ALL-CONSP-OF-CDR))
 (61 61 (:TYPE-PRESCRIPTION LEN))
 (52 2 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (49 4 (:DEFINITION TRUE-LISTP))
 (48 24 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (45 24 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (32 2 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (30 30 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (27 1 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (25 1 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (24 24 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (24 24 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (24 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (22 11 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (20 20 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (20 10 (:REWRITE DEFAULT-+-2))
 (18 18 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (18 15 (:REWRITE DEFAULT-<-1))
 (18 9 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (17 9 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION AXE-TREEP))
 (15 15 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (14 14 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (13 9 (:REWRITE USE-ALL-DARGP))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE USE-ALL-DARGP-2))
 (9 9 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (9 9 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (8 1 (:REWRITE ALL-DARGP-OF-CDR))
 (6 6 (:TYPE-PRESCRIPTION AXE-TREE-LISTP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (3 3 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (1 1 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (1 1 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (1 1 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (1 1 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 )
(DARGP-LESS-THAN-OF-MAYBE-REPLACE-VAR
 (156 39 (:REWRITE DEFAULT-CAR))
 (128 19 (:REWRITE DEFAULT-CDR))
 (122 26 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (52 26 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (48 48 (:TYPE-PRESCRIPTION ALL-CONSP))
 (44 44 (:REWRITE USE-ALL-CONSP-2))
 (44 44 (:REWRITE USE-ALL-CONSP))
 (26 26 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (24 24 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (24 12 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (14 7 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (12 12 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (9 9 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION AXE-TREEP))
 )
(MYQUOTEP-OF-MAYBE-REPLACE-VAR
 (90 6 (:DEFINITION STRIP-CDRS))
 (72 18 (:REWRITE DEFAULT-CDR))
 (63 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (30 6 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (18 18 (:REWRITE USE-ALL-CONSP-2))
 (18 18 (:REWRITE USE-ALL-CONSP))
 (12 12 (:TYPE-PRESCRIPTION ALL-CONSP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (3 1 (:REWRITE USE-ALL-DARGP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (1 1 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 )
(AXE-TREEP-OF-MAYBE-REPLACE-VAR
 (180 12 (:DEFINITION STRIP-CDRS))
 (135 27 (:REWRITE DEFAULT-CDR))
 (126 6 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (60 12 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (33 33 (:REWRITE USE-ALL-CONSP-2))
 (33 33 (:REWRITE USE-ALL-CONSP))
 (24 24 (:TYPE-PRESCRIPTION ALL-CONSP))
 (24 12 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (17 1 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (16 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (12 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 6 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (12 6 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (6 6 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (6 2 (:REWRITE USE-ALL-DARGP))
 (5 5 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (4 2 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (3 2 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MYQUOTEP))
 (2 2 (:REWRITE USE-ALL-DARGP-2))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (2 2 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (2 2 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 )
(BOUNDED-AXE-TREEP-OF-MAYBE-REPLACE-VAR
 (51 22 (:REWRITE DEFAULT-CDR))
 (48 6 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (45 3 (:DEFINITION STRIP-CDRS))
 (38 3 (:DEFINITION LEN))
 (26 1 (:DEFINITION SYMBOL-LISTP))
 (24 18 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE USE-ALL-CONSP-2))
 (20 20 (:REWRITE USE-ALL-CONSP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:TYPE-PRESCRIPTION ALL-CONSP))
 (16 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (14 1 (:DEFINITION TRUE-LISTP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (12 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 3 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION AXE-TREEP))
 (2 2 (:REWRITE BOUNDED-AXE-TREEP-MONO))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 )
