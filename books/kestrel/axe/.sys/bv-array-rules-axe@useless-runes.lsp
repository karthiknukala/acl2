(BV-ARRAYP$-KNOWN-BOOLEANS-JUSTIFICATION)
(BV-ARRAY-WRITE-TRIM-VALUE-ALL
 (97 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (95 6 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (55 6 (:REWRITE BVCHOP-IDENTITY))
 (45 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-UPDATE-NTH))
 (44 29 (:REWRITE DEFAULT-<-2))
 (44 5 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (40 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (38 2 (:REWRITE UNSIGNED-BYTE-P-BVCHOP-SAME))
 (32 29 (:REWRITE DEFAULT-<-1))
 (32 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (29 29 (:REWRITE USE-ALL-<-2))
 (29 29 (:REWRITE USE-ALL-<))
 (29 29 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (28 28 (:REWRITE USE-ALL-<=-2))
 (28 28 (:REWRITE USE-ALL-<=))
 (28 28 (:REWRITE BOUND-WHEN-USB))
 (25 3 (:REWRITE TAKE-DOES-NOTHING))
 (19 19 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (19 19 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (16 16 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (15 5 (:REWRITE COMMUTATIVITY-OF-+))
 (15 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (13 13 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (13 13 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (13 1 (:REWRITE LEN-OF-BVCHOP-LIST))
 (12 12 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (11 11 (:TYPE-PRESCRIPTION NATP))
 (11 5 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (11 5 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (10 4 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (10 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (10 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (9 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 2 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (7 7 (:REWRITE UBP-LONGER-BETTER))
 (7 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (7 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TAKE-2))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (6 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (4 4 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (4 4 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE USE-ALL-RATIONALP-2))
 (3 3 (:REWRITE USE-ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (2 2 (:REWRITE CONSP-OF-TAKE))
 (2 2 (:REWRITE CONSP-FROM-LEN-BOUND))
 )
(BV-ARRAY-WRITE-TRIM-VALUE)
(CONS-BECOMES-BV-ARRAY-WRITE-GEN
 (13 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (10 1 (:DEFINITION MEMBER-EQUAL))
 (6 3 (:REWRITE DEFAULT-+-2))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE BOUND-WHEN-USB))
 (5 3 (:REWRITE DEFAULT-<-1))
 (5 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (4 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE USE-ALL-<=-2))
 (3 3 (:REWRITE USE-ALL-<=))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE USE-ALL-<))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (3 3 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (2 2 (:REWRITE CONSP-FROM-LEN-BOUND))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (2 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-TIGHTEN2
 (198 12 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (86 63 (:REWRITE DEFAULT-<-1))
 (75 63 (:REWRITE DEFAULT-<-2))
 (64 64 (:REWRITE BOUND-WHEN-USB))
 (63 63 (:REWRITE USE-ALL-<=-2))
 (63 63 (:REWRITE USE-ALL-<=))
 (63 63 (:REWRITE USE-ALL-<-2))
 (63 63 (:REWRITE USE-ALL-<))
 (63 63 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (61 36 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (32 6 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (29 24 (:REWRITE DEFAULT-+-2))
 (29 24 (:REWRITE DEFAULT-+-1))
 (27 27 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (27 27 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (27 27 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (27 27 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (21 7 (:REWRITE COMMUTATIVITY-OF-+))
 (20 6 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (18 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (15 4 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (14 7 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (13 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (12 12 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (12 12 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (10 10 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (10 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (10 2 (:REWRITE BVCHOP-IDENTITY))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (7 2 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (5 5 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (4 4 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (4 4 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 4 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE CONSP-FROM-LEN-BOUND))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 1 (:REWRITE CONSP-OF-TRUE-LIST-FIX))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(CONS-OF-BV-ARRAY-WRITE-GEN
 (4047 182 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2665 49 (:REWRITE UNSIGNED-BYTE-P-OF-NTH))
 (2063 58 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-UPDATE-NTH))
 (2062 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CONS))
 (1699 235 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (1518 894 (:REWRITE DEFAULT-<-1))
 (1435 894 (:REWRITE DEFAULT-<-2))
 (1112 18 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (1101 10 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (1084 82 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (963 54 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (942 43 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (939 1 (:REWRITE UNSIGNED-BYTE-P-OF-IF))
 (903 104 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (902 902 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (894 894 (:REWRITE USE-ALL-<-2))
 (894 894 (:REWRITE USE-ALL-<))
 (894 43 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (885 103 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (871 103 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (742 742 (:REWRITE BOUND-WHEN-USB))
 (713 713 (:REWRITE USE-ALL-<=-2))
 (713 713 (:REWRITE USE-ALL-<=))
 (708 579 (:REWRITE DEFAULT-+-2))
 (674 48 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (618 579 (:REWRITE DEFAULT-+-1))
 (427 20 (:REWRITE ACL2-NUMBERP-OF-NTH-WHEN-ALL-DARGP))
 (409 23 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TAKE-2))
 (406 406 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (405 47 (:REWRITE CONSP-OF-TAKE))
 (393 7 (:REWRITE LEN-OF-NTHCDR))
 (385 385 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (380 12 (:REWRITE CONSP-OF-NTHCDR))
 (373 49 (:REWRITE UNSIGNED-BYTE-P-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP-2))
 (367 367 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (367 367 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (318 78 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (235 235 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (235 235 (:REWRITE UBP-LONGER-BETTER))
 (225 20 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (216 72 (:REWRITE ALL-INTEGERP-OF-UPDATE-NTH))
 (208 208 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (206 206 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (206 206 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (187 61 (:REWRITE ZP-OPEN))
 (184 184 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (184 184 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (184 184 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (177 98 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (171 171 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (159 159 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (156 156 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (156 78 (:REWRITE ALL-NATP-IMPLIES-ALL-INTEGERP-CHEAP))
 (149 8 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTHCDR))
 (130 130 (:TYPE-PRESCRIPTION POSP))
 (130 8 (:REWRITE CONSP-OF-BVCHOP-LIST))
 (128 2 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CONS))
 (114 38 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (112 112 (:REWRITE <-OF-NTH-WHEN-BOUNDED-DARG-LISTP-FREE))
 (103 103 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (103 103 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (103 103 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (82 82 (:REWRITE INTEGERP-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP))
 (82 82 (:REWRITE INTEGERP-OF-NTH-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (82 82 (:REWRITE INTEGERP-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (82 20 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (78 78 (:TYPE-PRESCRIPTION ALL-NATP))
 (78 78 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (78 78 (:REWRITE ALL-INTEGERP-WHEN-UNSIGNED-BYTE-LISTP))
 (74 2 (:REWRITE FIRSTN-WHEN-<=-OF-LEN))
 (67 38 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (60 24 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (59 59 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (59 59 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (59 59 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (59 59 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (58 58 (:REWRITE CONSP-FROM-LEN-BOUND))
 (57 57 (:REWRITE NOT-<-OF-NTH-WHEN-BOUNDED-DARG-LISTP-GEN-CONSTANT))
 (54 6 (:REWRITE UNSIGNED-BYTE-LISTP-OF-NTHCDR))
 (44 44 (:REWRITE DEFAULT-UNARY-MINUS))
 (43 43 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (43 43 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (42 42 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (42 42 (:REWRITE USE-ALL-CONSP-2))
 (42 42 (:REWRITE USE-ALL-CONSP))
 (40 40 (:TYPE-PRESCRIPTION ALL-DARGP))
 (40 20 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (40 2 (:REWRITE TAKE-DOES-NOTHING-REWRITE))
 (38 38 (:REWRITE USE-ALL-RATIONALP-2))
 (38 38 (:REWRITE USE-ALL-RATIONALP))
 (38 38 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (38 38 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (38 38 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (38 38 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (30 1 (:DEFINITION NTH))
 (28 7 (:REWRITE DEFAULT-*-2))
 (23 23 (:TYPE-PRESCRIPTION ZP))
 (22 11 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (20 20 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (18 2 (:REWRITE <-OF-EXPT-AND-EXPT))
 (17 3 (:REWRITE DEFAULT-CDR))
 (17 3 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (13 13 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (12 3 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (9 9 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTHCDR-LONGER))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (5 5 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (3 3 (:REWRITE BVCHOP-BOUND))
 (3 3 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (2 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 )
(MYIF-OF-BV-ARRAY-WRITE-ARG1-SAFE
 (160 7 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (116 14 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (68 4 (:REWRITE CONSP-OF-TAKE))
 (63 7 (:REWRITE ZP-OPEN))
 (60 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (58 2 (:REWRITE UNSIGNED-BYTE-P-OF-IF))
 (54 8 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (54 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-UPDATE-NTH))
 (47 34 (:REWRITE DEFAULT-<-1))
 (46 34 (:REWRITE DEFAULT-<-2))
 (40 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (38 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (34 34 (:REWRITE USE-ALL-<=-2))
 (34 34 (:REWRITE USE-ALL-<=))
 (34 34 (:REWRITE USE-ALL-<-2))
 (34 34 (:REWRITE USE-ALL-<))
 (34 34 (:REWRITE BOUND-WHEN-USB))
 (34 34 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (32 2 (:REWRITE LEN-OF-BVCHOP-LIST))
 (30 3 (:DEFINITION NTH))
 (30 3 (:DEFINITION MEMBER-EQUAL))
 (26 26 (:REWRITE CONSP-FROM-LEN-BOUND))
 (24 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (21 21 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (21 21 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (21 7 (:REWRITE COMMUTATIVITY-OF-+))
 (20 18 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (18 4 (:REWRITE UNSIGNED-BYTE-P-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP-2))
 (17 17 (:REWRITE DEFAULT-+-2))
 (17 17 (:REWRITE DEFAULT-+-1))
 (16 16 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (16 16 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (16 16 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (16 16 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (16 16 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (16 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (14 2 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TAKE-2))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (12 12 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (12 12 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (12 6 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE DEFAULT-CAR))
 (10 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (8 8 (:REWRITE UBP-LONGER-BETTER))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (3 3 (:REWRITE MYIF-WHEN-NOT-NIL))
 (3 3 (:REWRITE MYIF-WHEN-NIL))
 (3 3 (:REWRITE MYIF-OF-CONSTANT-WHEN-NOT-NIL))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 )
(MYIF-OF-BV-ARRAY-WRITE-ARG2-SAFE
 (131 9 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (74 2 (:REWRITE UNSIGNED-BYTE-P-OF-IF))
 (68 21 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (67 8 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (62 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-UPDATE-NTH))
 (53 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (41 6 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (40 4 (:DEFINITION MEMBER-EQUAL))
 (38 10 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (35 32 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (34 31 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE USE-ALL-<=-2))
 (31 31 (:REWRITE USE-ALL-<=))
 (31 31 (:REWRITE USE-ALL-<-2))
 (31 31 (:REWRITE USE-ALL-<))
 (31 31 (:REWRITE DEFAULT-<-1))
 (31 31 (:REWRITE BOUND-WHEN-USB))
 (31 31 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (30 3 (:DEFINITION NTH))
 (29 29 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (29 29 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (29 29 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (29 29 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (28 4 (:REWRITE UNSIGNED-BYTE-P-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP-2))
 (25 25 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (25 25 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (25 25 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (25 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (25 3 (:REWRITE LEN-OF-BVCHOP-LIST))
 (24 8 (:REWRITE COMMUTATIVITY-OF-+))
 (23 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (22 22 (:REWRITE CONSP-FROM-LEN-BOUND))
 (20 20 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (20 20 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (20 20 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (20 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (19 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE USE-ALL-CONSP-2))
 (16 16 (:REWRITE USE-ALL-CONSP))
 (12 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (10 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (9 9 (:REWRITE UBP-LONGER-BETTER))
 (9 9 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (9 9 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (9 9 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TAKE-2))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (4 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 2 (:REWRITE CONSP-OF-TRUE-LIST-FIX))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE MYIF-WHEN-NOT-NIL))
 (3 3 (:REWRITE MYIF-WHEN-NIL))
 (3 3 (:REWRITE MYIF-OF-CONSTANT-WHEN-NOT-NIL))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 2 (:REWRITE CONSP-OF-TAKE))
 )
(BV-ARRAY-WRITE-TIGHTEN-WHEN-QUOTEP-DATA
 (102 9 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (44 2 (:REWRITE BVCHOP-IDENTITY))
 (38 28 (:REWRITE DEFAULT-+-2))
 (38 28 (:REWRITE DEFAULT-+-1))
 (35 33 (:REWRITE DEFAULT-<-2))
 (34 34 (:REWRITE BOUND-WHEN-USB))
 (34 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (33 33 (:REWRITE USE-ALL-<=-2))
 (33 33 (:REWRITE USE-ALL-<=))
 (33 33 (:REWRITE USE-ALL-<-2))
 (33 33 (:REWRITE USE-ALL-<))
 (33 33 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (33 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (32 17 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (29 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (29 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (28 6 (:REWRITE COMMUTATIVITY-OF-+))
 (27 3 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (23 23 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (23 3 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (20 2 (:DEFINITION MEMBER-EQUAL))
 (18 18 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (18 18 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (18 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (16 14 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (15 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (14 8 (:REWRITE DEFAULT-CDR))
 (13 6 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (13 5 (:REWRITE UBP-LONGER-BETTER))
 (12 12 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (12 12 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (12 2 (:REWRITE LEN-OF-BVCHOP-LIST))
 (12 2 (:REWRITE DEFAULT-*-2))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE FOLD-CONSTS-IN-+))
 (9 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (9 1 (:REWRITE <-OF-EXPT-AND-EXPT))
 (8 4 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (7 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (6 6 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (6 6 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (6 4 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (5 5 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (5 5 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 2 (:REWRITE UNICITY-OF-0))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:DEFINITION FIX))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-NATP))
 (1 1 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 )
(BV-ARRAY-WRITE-DOES-NOTHING-CHEAP
 (90 6 (:REWRITE BVCHOP-IDENTITY))
 (66 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (44 5 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (44 5 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (42 3 (:REWRITE UPDATE-NTH-WITH-LAST-VAL-GEN))
 (38 2 (:REWRITE UNSIGNED-BYTE-P-BVCHOP-SAME))
 (37 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-UPDATE-NTH))
 (36 20 (:REWRITE DEFAULT-<-2))
 (31 4 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (24 3 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (23 20 (:REWRITE DEFAULT-<-1))
 (23 4 (:REWRITE UNSIGNED-BYTE-P-OF-NTH))
 (20 20 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (20 20 (:REWRITE USE-ALL-<-2))
 (20 20 (:REWRITE USE-ALL-<))
 (20 20 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (20 2 (:DEFINITION NTH))
 (19 19 (:REWRITE USE-ALL-<=-2))
 (19 19 (:REWRITE USE-ALL-<=))
 (19 19 (:REWRITE BOUND-WHEN-USB))
 (19 10 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (14 4 (:REWRITE UNSIGNED-BYTE-P-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP-2))
 (13 11 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (13 3 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (12 12 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 12 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (12 12 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (12 12 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (12 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (11 11 (:TYPE-PRESCRIPTION NATP))
 (11 5 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (11 3 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (10 5 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (10 5 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (10 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (9 9 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (9 9 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (9 9 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (9 9 (:REWRITE CONSP-FROM-LEN-BOUND))
 (9 3 (:REWRITE COMMUTATIVITY-OF-+))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (7 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (6 6 (:REWRITE UBP-LONGER-BETTER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (6 6 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (6 6 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (6 3 (:REWRITE ALL-NATP-IMPLIES-ALL-INTEGERP-CHEAP))
 (5 5 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (5 3 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (5 1 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 3 (:TYPE-PRESCRIPTION ALL-NATP))
 (3 3 (:REWRITE USE-ALL-RATIONALP-2))
 (3 3 (:REWRITE USE-ALL-RATIONALP))
 (3 3 (:REWRITE INTEGERP-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE INTEGERP-OF-NTH-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (3 3 (:REWRITE INTEGERP-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (3 3 (:REWRITE ALL-INTEGERP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (2 1 (:REWRITE CONSP-OF-TRUE-LIST-FIX))
 (1 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 )
(BV-ARRAY-READ-TRIM-INDEX-DAG-256
 (23 1 (:REWRITE BVCHOP-IDENTITY))
 (15 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (13 3 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (12 2 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (3 3 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (3 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (2 2 (:REWRITE USE-ALL-RATIONALP-2))
 (2 2 (:REWRITE USE-ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (1 1 (:REWRITE UBP-LONGER-BETTER))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 )
(MYIF-BECOMES-BV-ARRAY-IF-AXE
 (40 40 (:TYPE-PRESCRIPTION MYIF))
 (16 4 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (4 4 (:REWRITE CONSP-FROM-LEN-BOUND))
 (4 4 (:REWRITE BV-ARRAYP-CONSTANT-OPENER))
 (2 2 (:REWRITE MYIF-WHEN-NIL))
 (2 2 (:REWRITE MYIF-OF-CONSTANT-WHEN-NOT-NIL))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (1 1 (:REWRITE EQUAL-OF-MYIF-ARG2-SAFE))
 (1 1 (:REWRITE EQUAL-OF-MYIF-ARG1-SAFE))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BV-ARRAY-IF-CONSTANT-OPENER))
 )
(UPDATE-NTH-BECOMES-BV-ARRAY-WRITE-AXE
 (6 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(BV-ARRAY-READ-SHORTEN-AXE
 (48 48 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
