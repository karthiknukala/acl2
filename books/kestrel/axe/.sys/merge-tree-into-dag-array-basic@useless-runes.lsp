(MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (3802 38 (:DEFINITION INTEGER-ABS))
 (3375 69 (:REWRITE USE-ALL-<-FOR-CAR))
 (3087 42 (:DEFINITION NAT-LISTP))
 (2028 33 (:REWRITE ALL-NATP-OF-CDR))
 (1959 39 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (1926 18 (:REWRITE ALL-<-OF-CDR))
 (1923 66 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (1638 39 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (1089 42 (:DEFINITION NATP))
 (508 213 (:REWRITE DEFAULT-+-2))
 (477 42 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (378 378 (:TYPE-PRESCRIPTION NAT-LISTP))
 (305 213 (:REWRITE DEFAULT-+-1))
 (304 19 (:DEFINITION LENGTH))
 (228 228 (:TYPE-PRESCRIPTION ALL-NATP))
 (195 195 (:TYPE-PRESCRIPTION ALL-<))
 (190 19 (:DEFINITION LEN))
 (138 69 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (132 66 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (128 110 (:REWRITE DEFAULT-<-2))
 (127 127 (:REWRITE USE-ALL-CONSP-2))
 (127 127 (:REWRITE USE-ALL-CONSP))
 (114 110 (:REWRITE DEFAULT-<-1))
 (111 66 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (110 110 (:REWRITE USE-ALL-<=-2))
 (110 110 (:REWRITE USE-ALL-<=))
 (110 110 (:REWRITE USE-ALL-<-2))
 (110 110 (:REWRITE USE-ALL-<))
 (110 110 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (110 110 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (104 104 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (87 6 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (78 3 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (69 69 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (67 67 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (66 66 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (66 39 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (51 51 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (51 51 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (42 42 (:REWRITE USE-ALL-NATP-2))
 (42 42 (:REWRITE USE-ALL-NATP))
 (42 42 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (42 42 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (42 9 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (42 6 (:REWRITE ALL-RATIONALP-OF-CDR))
 (42 6 (:REWRITE ALL-CONSP-OF-CDR))
 (39 39 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (39 39 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (39 39 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (39 39 (:REWRITE ALL-<-TRANSITIVE))
 (39 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (38 38 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (38 38 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (38 38 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (38 38 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (24 24 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (24 24 (:TYPE-PRESCRIPTION ALL-CONSP))
 (24 24 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (24 24 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (19 19 (:TYPE-PRESCRIPTION LEN))
 (19 19 (:REWRITE USE-ALL-RATIONALP-2))
 (19 19 (:REWRITE USE-ALL-RATIONALP))
 (19 19 (:REWRITE DEFAULT-REALPART))
 (19 19 (:REWRITE DEFAULT-NUMERATOR))
 (19 19 (:REWRITE DEFAULT-IMAGPART))
 (19 19 (:REWRITE DEFAULT-DENOMINATOR))
 (19 19 (:REWRITE DEFAULT-COERCE-2))
 (19 19 (:REWRITE DEFAULT-COERCE-1))
 (18 18 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (18 6 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (12 12 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (12 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (9 9 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (6 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (6 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 )
(FLAG-MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (4608 60 (:DEFINITION INTEGER-ABS))
 (3927 89 (:REWRITE USE-ALL-<-FOR-CAR))
 (3559 54 (:DEFINITION NAT-LISTP))
 (2205 43 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (2153 78 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (2046 35 (:REWRITE ALL-NATP-OF-CDR))
 (1926 18 (:REWRITE ALL-<-OF-CDR))
 (1912 43 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (1301 54 (:DEFINITION NATP))
 (719 315 (:REWRITE DEFAULT-+-2))
 (557 54 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (480 30 (:DEFINITION LENGTH))
 (450 450 (:TYPE-PRESCRIPTION NAT-LISTP))
 (447 315 (:REWRITE DEFAULT-+-1))
 (300 30 (:DEFINITION LEN))
 (266 266 (:TYPE-PRESCRIPTION ALL-NATP))
 (239 239 (:TYPE-PRESCRIPTION ALL-<))
 (178 89 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (174 151 (:REWRITE DEFAULT-<-2))
 (158 151 (:REWRITE DEFAULT-<-1))
 (156 156 (:REWRITE USE-ALL-CONSP-2))
 (156 156 (:REWRITE USE-ALL-CONSP))
 (156 78 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (151 151 (:REWRITE USE-ALL-<=-2))
 (151 151 (:REWRITE USE-ALL-<=))
 (151 151 (:REWRITE USE-ALL-<-2))
 (151 151 (:REWRITE USE-ALL-<))
 (151 151 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (151 151 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (142 142 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (123 78 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (107 10 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (98 7 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (89 89 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (82 82 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (78 78 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (70 43 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (60 60 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (60 60 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (60 60 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
 (59 59 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (59 59 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (54 54 (:REWRITE USE-ALL-NATP-2))
 (54 54 (:REWRITE USE-ALL-NATP))
 (54 54 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (48 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (46 46 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (46 13 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (43 43 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (43 43 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (43 43 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (43 43 (:REWRITE ALL-<-TRANSITIVE))
 (43 16 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (42 6 (:REWRITE ALL-RATIONALP-OF-CDR))
 (42 6 (:REWRITE ALL-CONSP-OF-CDR))
 (32 32 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (32 32 (:TYPE-PRESCRIPTION ALL-CONSP))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (30 30 (:REWRITE USE-ALL-RATIONALP-2))
 (30 30 (:REWRITE USE-ALL-RATIONALP))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (26 26 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (24 24 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (24 24 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (18 6 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (16 16 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (13 13 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 10 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-MERGE-TREE-INTO-DAG-ARRAY-BASIC-EQUIVALENCES)
(FLAG-LEMMA-FOR-MERGE-TREE-INTO-DAG-ARRAY-BASIC-RETURN-TYPE
 (195353 343 (:REWRITE AXE-TREEP-OF-CAR))
 (169299 2739 (:DEFINITION NAT-LISTP))
 (166644 562 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (156394 222 (:DEFINITION DARGP))
 (135920 1581 (:REWRITE USE-ALL-<-FOR-CAR))
 (128728 3901 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (117395 3585 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (79474 1867 (:REWRITE ALL-NATP-OF-CDR))
 (70168 1350 (:REWRITE ALL-<-OF-CDR))
 (61207 2599 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (53838 2599 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (45951 1010 (:DEFINITION PSEUDO-TERM-LISTP))
 (45281 4436 (:DEFINITION MEMBER-EQUAL))
 (44259 3594 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (41758 32494 (:REWRITE DEFAULT-CAR))
 (40643 629 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (35438 31532 (:REWRITE DEFAULT-CDR))
 (30744 2149 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (22176 22176 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (18480 18480 (:REWRITE USE-ALL-CONSP-2))
 (18480 18480 (:REWRITE USE-ALL-CONSP))
 (14731 4001 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (14051 1033 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (12486 629 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (12012 2149 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (10537 1861 (:REWRITE ALL-CONSP-OF-CDR))
 (9101 9101 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (8225 4112 (:REWRITE DEFAULT-+-2))
 (8002 8002 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8002 8002 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7802 3901 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (7699 1082 (:REWRITE ALL-DARGP-OF-CDR))
 (7592 7592 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (7090 7090 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (7090 7090 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (7090 7090 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (5876 2687 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (5583 1861 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (4806 2691 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (4527 333 (:REWRITE USE-ALL-DARGP-FOR-CAR))
 (4298 2149 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4112 4112 (:REWRITE DEFAULT-+-1))
 (4078 34 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (4075 3901 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (4001 4001 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (3901 3901 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (3892 1908 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (3816 3816 (:TYPE-PRESCRIPTION ALL-DARGP))
 (3816 1908 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3648 1824 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (3648 1824 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (3648 1824 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (3593 3593 (:REWRITE USE-ALL-NATP-2))
 (3593 3593 (:REWRITE USE-ALL-NATP))
 (3198 1668 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (3162 1581 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (3150 3150 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2773 2773 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2721 2687 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2691 2691 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2691 2691 (:REWRITE ALL-<-TRANSITIVE))
 (2337 2337 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2149 2149 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2149 2149 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2149 2149 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2131 1637 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1982 1982 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1963 1963 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1908 1908 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (1908 1908 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (1834 1834 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1824 1824 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (1824 1824 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1748 1637 (:REWRITE DEFAULT-<-1))
 (1712 520 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1697 1637 (:REWRITE DEFAULT-<-2))
 (1695 3 (:REWRITE ALL-<-OF-CONS))
 (1637 1637 (:REWRITE USE-ALL-<-2))
 (1637 1637 (:REWRITE USE-ALL-<))
 (1634 1634 (:REWRITE USE-ALL-<=-2))
 (1634 1634 (:REWRITE USE-ALL-<=))
 (1591 1591 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1581 1581 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1532 1532 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1518 1518 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (1228 614 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (1228 614 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (1092 52 (:DEFINITION STRIP-CDRS))
 (1039 1039 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1014 1014 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (976 976 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (932 932 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (865 865 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (624 624 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (614 614 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (614 614 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (614 614 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (564 564 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (560 560 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (560 560 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (560 560 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (526 526 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (520 520 (:TYPE-PRESCRIPTION DARGP))
 (520 520 (:REWRITE USE-ALL-DARGP-2))
 (520 520 (:REWRITE USE-ALL-DARGP))
 (520 520 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (520 520 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (444 222 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (405 222 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (404 33 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (252 3 (:REWRITE ALL-<-OF-REVERSE-LIST))
 (239 39 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (162 54 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (154 77 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (144 4 (:REWRITE CONSP-OF-TAKE))
 (142 42 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (110 55 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (110 55 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (82 82 (:LINEAR ARRAY2P-LINEAR))
 (70 2 (:REWRITE ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (66 33 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (64 4 (:REWRITE ZP-OPEN))
 (50 6 (:REWRITE ALL-<-OF-TAKE))
 (40 1 (:REWRITE BOUND-ON-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-WITH-NAME-3-GEN))
 (38 38 (:REWRITE BOUNDED-AXE-TREEP-MONO))
 (36 36 (:REWRITE USE-ALL-RATIONALP-2))
 (36 36 (:REWRITE USE-ALL-RATIONALP))
 (20 10 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (19 14 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (16 16 (:TYPE-PRESCRIPTION PAIRLIS$-FAST-AUX))
 (16 16 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-NTH-0-AND-QUOTE))
 (14 10 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (14 10 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (12 12 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (12 10 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (10 4 (:REWRITE SYMBOL-LISTP-OF-TRUE-LIST-FIX))
 (9 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (8 8 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (8 8 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (8 4 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-WITH-NAME))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-PSEUDO-DAGP-AUX))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 1 (:REWRITE RATIONALP-OF-ALEN1-WHEN-ARRAY1P))
 (4 1 (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP))
 (3 3 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-LIST))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL-ALT))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 )
(MERGE-TREE-INTO-DAG-ARRAY-BASIC-RETURN-TYPE)
(MERGE-TREES-INTO-DAG-ARRAY-BASIC-RETURN-TYPE)
(MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (99560 96 (:REWRITE AXE-TREEP-OF-CAR))
 (83040 22 (:DEFINITION AXE-TREEP))
 (82156 112 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (80883 52 (:DEFINITION AXE-TREE-LISTP))
 (79195 112 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (64818 114 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (61714 59 (:DEFINITION DARGP))
 (59501 758 (:DEFINITION NAT-LISTP))
 (47554 771 (:REWRITE USE-ALL-<-FOR-CAR))
 (47292 506 (:DEFINITION NATP))
 (45052 1016 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (37577 985 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (27253 441 (:REWRITE ALL-NATP-OF-CDR))
 (22662 411 (:REWRITE ALL-<-OF-CDR))
 (21788 854 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (19726 854 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (15725 1282 (:DEFINITION MEMBER-EQUAL))
 (14643 998 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (10903 9192 (:REWRITE DEFAULT-CAR))
 (10635 8679 (:REWRITE DEFAULT-CDR))
 (7999 576 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (7416 250 (:DEFINITION PSEUDO-TERM-LISTP))
 (6410 6410 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6289 172 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (5238 5238 (:REWRITE USE-ALL-CONSP-2))
 (5238 5238 (:REWRITE USE-ALL-CONSP))
 (4974 330 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (3917 1020 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (3913 3913 (:TYPE-PRESCRIPTION ALL-NATP))
 (3569 107 (:DEFINITION MYQUOTEP))
 (3062 576 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (2984 107 (:DEFINITION QUOTEP))
 (2911 2911 (:TYPE-PRESCRIPTION ALL-<))
 (2903 172 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (2808 2808 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2600 446 (:REWRITE ALL-CONSP-OF-CDR))
 (2462 906 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (2328 1167 (:REWRITE DEFAULT-+-2))
 (2040 2040 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (2040 2040 (:TYPE-PRESCRIPTION ALL-CONSP))
 (2032 1016 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (1986 1986 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (1986 1986 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1986 1986 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (1889 48 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<))
 (1843 1843 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1786 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (1738 86 (:DEFINITION STRIP-CDRS))
 (1542 771 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1428 206 (:REWRITE ALL-DARGP-OF-CDR))
 (1350 675 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (1350 675 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (1350 675 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (1338 446 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (1304 1016 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (1283 107 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1167 1167 (:REWRITE DEFAULT-+-1))
 (1152 576 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1020 1020 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1016 1016 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (998 998 (:REWRITE USE-ALL-NATP-2))
 (998 998 (:REWRITE USE-ALL-NATP))
 (958 472 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (954 906 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (944 944 (:TYPE-PRESCRIPTION ALL-DARGP))
 (944 472 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (937 89 (:REWRITE USE-ALL-DARGP-FOR-CAR))
 (907 907 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (907 907 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (907 907 (:REWRITE ALL-<-TRANSITIVE))
 (819 803 (:REWRITE DEFAULT-<-2))
 (803 803 (:REWRITE USE-ALL-<=-2))
 (803 803 (:REWRITE USE-ALL-<=))
 (803 803 (:REWRITE USE-ALL-<-2))
 (803 803 (:REWRITE USE-ALL-<))
 (803 803 (:REWRITE DEFAULT-<-1))
 (803 803 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (803 803 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (787 787 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (771 771 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (752 376 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (730 730 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (727 727 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (691 691 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (688 688 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (675 675 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (675 675 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (592 296 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (592 296 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (576 576 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (576 576 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (576 576 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (548 548 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (520 520 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (472 472 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (472 472 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (458 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (402 45 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (397 397 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (373 373 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (331 331 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (322 322 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (320 320 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (315 315 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (296 296 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (296 296 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (288 8 (:REWRITE CONSP-OF-TAKE))
 (276 276 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (268 268 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (244 122 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (128 8 (:REWRITE ZP-OPEN))
 (118 59 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (117 59 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (114 114 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (114 114 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (112 112 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (107 107 (:TYPE-PRESCRIPTION DARGP))
 (107 107 (:REWRITE USE-ALL-DARGP-2))
 (107 107 (:REWRITE USE-ALL-DARGP))
 (107 107 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (107 107 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (107 107 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (107 107 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (107 107 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (100 1 (:REWRITE ALL-<-OF-REVERSE-LIST))
 (96 48 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (96 48 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (83 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-NOT-CONSP))
 (82 82 (:LINEAR ARRAY2P-LINEAR))
 (68 34 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (59 59 (:TYPE-PRESCRIPTION MYQUOTEP))
 (49 49 (:REWRITE BOUNDED-AXE-TREEP-MONO))
 (48 16 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (45 5 (:REWRITE ALL-<-OF-TAKE))
 (38 19 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (34 34 (:TYPE-PRESCRIPTION DARGP-LESS-THAN))
 (24 1 (:DEFINITION ASSOC-EQUAL))
 (17 5 (:REWRITE SYMBOL-LISTP-OF-TRUE-LIST-FIX))
 (16 16 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (16 16 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (8 7 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 )
