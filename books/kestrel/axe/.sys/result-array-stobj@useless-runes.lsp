(RESULT-ALISTP)
(RESULT-ALISTP-OF-CONS
 (308 74 (:REWRITE DEFAULT-CAR))
 (105 21 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (103 40 (:REWRITE DEFAULT-CDR))
 (63 21 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (57 57 (:REWRITE USE-ALL-CONSP-2))
 (57 57 (:REWRITE USE-ALL-CONSP))
 (56 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (42 42 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (42 42 (:TYPE-PRESCRIPTION ALL-CONSP))
 (42 21 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (26 26 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (21 21 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (21 21 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (21 21 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (21 21 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (21 21 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (15 15 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (12 2 (:REWRITE ALISTP-OF-CDR))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (10 5 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (8 8 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (8 8 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (4 2 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (4 2 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION MYQUOTEP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE USE-ALL-DARGP-2))
 (2 2 (:REWRITE USE-ALL-DARGP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (2 2 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 )
(RESULT-ALISTP-FORWARD-TO-ALISTP)
(RESULT-ALISTP-FORWARD-TO-SYMBOL-ALISTP
 (2073 36 (:REWRITE RESULT-ALISTP-FORWARD-TO-ALISTP))
 (1174 426 (:REWRITE DEFAULT-CAR))
 (432 70 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (391 173 (:REWRITE DEFAULT-CDR))
 (372 8 (:REWRITE ALISTP-OF-CDR))
 (280 26 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (260 70 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (184 184 (:REWRITE USE-ALL-CONSP-2))
 (184 184 (:REWRITE USE-ALL-CONSP))
 (172 172 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (172 172 (:TYPE-PRESCRIPTION ALL-CONSP))
 (140 70 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (131 131 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (110 110 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (90 18 (:REWRITE ALL-CONSP-OF-CDR))
 (86 86 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (86 86 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (72 72 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (70 70 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (70 70 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (70 70 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (54 18 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (52 26 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (52 26 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (48 24 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (36 36 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (36 36 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (32 16 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (26 26 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (26 26 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (22 22 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (16 8 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (16 8 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (12 8 (:REWRITE USE-ALL-DARGP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:TYPE-PRESCRIPTION MYQUOTEP))
 (8 8 (:REWRITE USE-ALL-NATP-2))
 (8 8 (:REWRITE USE-ALL-NATP))
 (8 8 (:REWRITE USE-ALL-DARGP-2))
 (8 8 (:REWRITE USE-ALL-<-2))
 (8 8 (:REWRITE USE-ALL-<))
 (8 8 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (8 8 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (8 8 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 )
(THEARRAYP-OF-MAKE-LIST-AC
 (8 6 (:REWRITE DEFAULT-CDR))
 (8 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE ZP-OPEN))
 )
(THEARRAYP-OF-UPDATE-NTH
 (78 2 (:REWRITE CDR-OF-UPDATE-NTH))
 (64 34 (:REWRITE DEFAULT-CDR))
 (37 7 (:REWRITE ZP-OPEN))
 (34 20 (:REWRITE DEFAULT-CAR))
 (31 31 (:REWRITE USE-ALL-CONSP-2))
 (31 31 (:REWRITE USE-ALL-CONSP))
 (26 18 (:REWRITE DEFAULT-+-2))
 (20 2 (:REWRITE CAR-OF-UPDATE-NTH))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE USE-ALL-<-2))
 (13 13 (:REWRITE USE-ALL-<))
 (13 13 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 )
(RESULT-ARRAY-STOBJP-OF-UPDATE-THEARRAYI
 (10 1 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP))
 (9 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (9 1 (:DEFINITION THEARRAYP))
 (5 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE CAR-OF-NTH-0-WHEN-PSEUDO-DAGP))
 (3 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (2 2 (:TYPE-PRESCRIPTION ALL-DARGP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE LEN-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 )
(THEARRAY-LENGTH-OF-UPDATE-THEARRAYI
 (21 3 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP))
 (10 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (6 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (5 4 (:REWRITE DEFAULT-<-1))
 (5 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (4 4 (:TYPE-PRESCRIPTION ALL-DARGP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (4 2 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3 3 (:REWRITE LEN-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(THEARRAYI-WHEN-NOT-NATP
 (16 8 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE NTH-0-OF-NTH-0-WHEN-PSEUDO-DAGP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(UPDATE-THEARRAYI-WHEN-NOT-NATP
 (16 8 (:REWRITE DEFAULT-CDR))
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (4 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(THEARRAYI-OF-UPDATE-THEARRAYI-SAME
 (12 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (7 3 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (6 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 )
(THEARRAYI-OF-UPDATE-THEARRAYI-DIFF
 (75 30 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (60 30 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (35 15 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (15 15 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:REWRITE USE-ALL-<-2))
 (9 9 (:REWRITE USE-ALL-<))
 (9 9 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 4 (:REWRITE NTH-0-OF-NTH-0-WHEN-PSEUDO-DAGP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(THEARRAYI-OF-UPDATE-THEARRAYI-SPLIT
 (40 32 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE USE-ALL-<-2))
 (32 32 (:REWRITE USE-ALL-<))
 (32 32 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (26 26 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (18 3 (:DEFINITION NATP))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE USE-ALL-NATP-2))
 (3 3 (:REWRITE USE-ALL-NATP))
 )
(UPDATE-THEARRAYI-OF-UPDATE-THEARRAYI-SAME
 (9 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (5 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(UPDATE-THEARRAYI-OF-UPDATE-THEARRAYI-DIFF
 (80 20 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (50 20 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (40 20 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (20 20 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (10 10 (:REWRITE USE-ALL-<-2))
 (10 10 (:REWRITE USE-ALL-<))
 (10 10 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(UPDATE-THEARRAYI-OF-UPDATE-THEARRAYI-SPLIT
 (83 34 (:REWRITE DEFAULT-CDR))
 (46 23 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (35 23 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (23 23 (:TYPE-PRESCRIPTION LEN))
 (23 23 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (18 12 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE USE-ALL-CONSP-2))
 (17 17 (:REWRITE USE-ALL-CONSP))
 (16 1 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE USE-ALL-<-2))
 (12 12 (:REWRITE USE-ALL-<))
 (12 12 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-THEARRAYI-OF-UPDATE-THEARRAYI-SAME-VALUES
 (16 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (10 4 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 )
(RESULT-ALISTP-OF-NTH-WHEN-THEARRAYP
 (12 6 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (10 10 (:REWRITE USE-ALL-CONSP-2))
 (10 10 (:REWRITE USE-ALL-CONSP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(RESULT-ALISTP-OF-THEARRAYI)
(THEARRAYP-OF-RESIZE-LIST
 (20 15 (:REWRITE DEFAULT-CDR))
 (16 14 (:REWRITE DEFAULT-CAR))
 (12 6 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (11 11 (:REWRITE USE-ALL-CONSP-2))
 (11 11 (:REWRITE USE-ALL-CONSP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE USE-ALL-<-2))
 (9 9 (:REWRITE USE-ALL-<))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (8 1 (:REWRITE CAR-OF-RESIZE-LIST))
 (7 2 (:REWRITE CONSP-OF-RESIZE-LIST))
 (5 1 (:DEFINITION POSP))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(RESULT-ARRAY-STOBJP-OF-RESIZE-THEARRAY
 (6 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (3 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (3 3 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(THEARRAY-LENGTH-OF-RESIZE-THEARRAY
 (6 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (3 1 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION RESIZE-LIST))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 )
(THEARRAYI-OF-RESIZE-THEARRAY
 (20 2 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP))
 (12 10 (:REWRITE DEFAULT-<-2))
 (12 7 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (12 7 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (10 10 (:REWRITE USE-ALL-<-2))
 (10 10 (:REWRITE USE-ALL-<))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 7 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (6 6 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (6 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION ALL-DARGP))
 (4 2 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 1 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION RESIZE-LIST))
 (2 2 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (2 2 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(RESIZE-THEARRAY-OF-UPDATE-THEARRAYI
 (20 2 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP))
 (16 6 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (14 2 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (12 4 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (11 1 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE USE-ALL-<-2))
 (8 8 (:REWRITE USE-ALL-<))
 (8 8 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE USE-ALL-CONSP-2))
 (7 7 (:REWRITE USE-ALL-CONSP))
 (6 6 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (6 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (4 4 (:TYPE-PRESCRIPTION ALL-DARGP))
 (4 2 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (2 2 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 )
(RESULT-ARRAY-STOBJP-OF-CREATE-RESULT-ARRAY-STOBJ
 (1 1 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(ALISTP-OF-NTH-WHEN-THEARRAYP
 (22 22 (:REWRITE USE-ALL-CONSP-2))
 (22 22 (:REWRITE USE-ALL-CONSP))
 (21 5 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (18 12 (:REWRITE DEFAULT-+-2))
 (17 11 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-CAR))
 (13 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (12 7 (:REWRITE ZP-OPEN))
 (11 11 (:REWRITE USE-ALL-<-2))
 (11 11 (:REWRITE USE-ALL-<))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7 7 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (7 7 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (5 5 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (5 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (5 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(ALISTP-OF-THEARRAYI
 (447 1 (:DEFINITION THEARRAYP))
 (439 1 (:DEFINITION RESULT-ALISTP))
 (259 1 (:DEFINITION SUBSETP-EQUAL))
 (252 7 (:DEFINITION STRIP-CARS))
 (252 4 (:DEFINITION MEMBER-EQUAL))
 (148 43 (:REWRITE DEFAULT-CAR))
 (110 22 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (70 2 (:DEFINITION STRIP-CDRS))
 (66 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (50 1 (:DEFINITION ALISTP))
 (48 18 (:REWRITE DEFAULT-CDR))
 (45 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (44 44 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (44 44 (:TYPE-PRESCRIPTION ALL-CONSP))
 (44 22 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (35 35 (:REWRITE USE-ALL-CONSP-2))
 (35 35 (:REWRITE USE-ALL-CONSP))
 (31 2 (:DEFINITION LEN))
 (23 23 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (22 22 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (22 22 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (18 18 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (12 3 (:REWRITE RESULT-ALISTP-FORWARD-TO-ALISTP))
 (10 1 (:REWRITE ALISTP-OF-CDR))
 (9 9 (:TYPE-PRESCRIPTION RESULT-ALISTP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (5 3 (:REWRITE DEFAULT-+-2))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION STRIP-CARS))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:TYPE-PRESCRIPTION ALL-DARGP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 )
(SYMBOL-ALISTP-OF-NTH-WHEN-THEARRAYP
 (22 22 (:REWRITE DEFAULT-CAR))
 (20 4 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (19 19 (:REWRITE USE-ALL-CONSP-2))
 (19 19 (:REWRITE USE-ALL-CONSP))
 (16 10 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 9 (:REWRITE DEFAULT-+-2))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (12 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (10 10 (:REWRITE USE-ALL-<-2))
 (10 10 (:REWRITE USE-ALL-<))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (7 7 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(SYMBOL-ALISTP-OF-THEARRAYI
 (447 1 (:DEFINITION THEARRAYP))
 (439 1 (:DEFINITION RESULT-ALISTP))
 (259 1 (:DEFINITION SUBSETP-EQUAL))
 (252 7 (:DEFINITION STRIP-CARS))
 (252 4 (:DEFINITION MEMBER-EQUAL))
 (148 43 (:REWRITE DEFAULT-CAR))
 (110 22 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (70 2 (:DEFINITION STRIP-CDRS))
 (66 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (50 1 (:DEFINITION ALISTP))
 (48 18 (:REWRITE DEFAULT-CDR))
 (45 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (44 44 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (44 44 (:TYPE-PRESCRIPTION ALL-CONSP))
 (44 22 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (35 35 (:REWRITE USE-ALL-CONSP-2))
 (35 35 (:REWRITE USE-ALL-CONSP))
 (31 2 (:DEFINITION LEN))
 (23 23 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (22 22 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (22 22 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (18 18 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (12 3 (:REWRITE RESULT-ALISTP-FORWARD-TO-ALISTP))
 (10 1 (:REWRITE ALISTP-OF-CDR))
 (9 9 (:TYPE-PRESCRIPTION RESULT-ALISTP))
 (5 5 (:TYPE-PRESCRIPTION ALISTP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (5 3 (:REWRITE DEFAULT-+-2))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION STRIP-CARS))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 1 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:TYPE-PRESCRIPTION ALL-DARGP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 )
(GET-FROM-RESULT-ARRAY-STOBJ)
(SET-IN-RESULT-ARRAY-STOBJ
 (33 17 (:REWRITE DEFAULT-<-2))
 (20 17 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE USE-ALL-<-2))
 (17 17 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(GET-FROM-RESULT-ARRAY-STOBJ-OF-SET-IN-RESULT-ARRAY-STOBJ-SAME
 (25 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE USE-ALL-<-2))
 (18 18 (:REWRITE USE-ALL-<))
 (18 18 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (8 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE THEARRAYI-OF-UPDATE-THEARRAYI-DIFF))
 )
(GET-RESULT
 (40 1 (:DEFINITION ALISTP))
 (36 1 (:DEFINITION SYMBOL-ALISTP))
 (10 10 (:TYPE-PRESCRIPTION RESULT-ALISTP))
 (10 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (9 3 (:REWRITE RESULT-ALISTP-FORWARD-TO-ALISTP))
 (9 1 (:REWRITE ALISTP-OF-CDR))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE RESULT-ALISTP-FORWARD-TO-SYMBOL-ALISTP))
 (6 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (4 4 (:TYPE-PRESCRIPTION ALL-CONSP))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (3 3 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 )
(SET-RESULT
 (41 28 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE USE-ALL-<-2))
 (28 28 (:REWRITE USE-ALL-<))
 (28 28 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE USE-ALL-DARGP-2))
 (15 15 (:REWRITE USE-ALL-DARGP))
 (15 15 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (15 15 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (15 15 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (6 6 (:REWRITE USE-ALL-CONSP-2))
 (6 6 (:REWRITE USE-ALL-CONSP))
 (6 6 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (6 3 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION MYQUOTEP))
 (3 3 (:REWRITE USE-ALL-NATP-2))
 (3 3 (:REWRITE USE-ALL-NATP))
 )
(LOOKUP-ARGS-IN-RESULT-ARRAY2
 (143 11 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<))
 (59 59 (:REWRITE USE-ALL-CONSP-2))
 (59 59 (:REWRITE USE-ALL-CONSP))
 (46 22 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (45 37 (:REWRITE DEFAULT-CDR))
 (44 22 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (40 5 (:REWRITE ALL-<-OF-CDR))
 (37 19 (:REWRITE DEFAULT-+-2))
 (34 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (33 33 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (33 33 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (32 32 (:TYPE-PRESCRIPTION ALL-<))
 (31 16 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (22 22 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (22 22 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (22 22 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (22 11 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (19 19 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (16 16 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (16 16 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (16 16 (:REWRITE ALL-<-TRANSITIVE))
 (12 12 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (12 12 (:TYPE-PRESCRIPTION ALL-CONSP))
 (11 11 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (11 11 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (6 6 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(CLEAR-RESULT-ARRAY-STOBJ-ELEMENTS
 (12 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE USE-ALL-<-2))
 (10 10 (:REWRITE USE-ALL-<))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CLEAR-RESULT-ARRAY-STOBJ)
