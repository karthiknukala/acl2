(MAYBE-DARGP)
(MAYBE-DARGP-WHEN-DARGP)
(RENUMBERING-ENTRIESP-OF-MAKE-LIST-AC
 (12 6 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE ZP-OPEN))
 )
(RENUMBERING-ENTRIESP-OF-UPDATE-NTH
 (70 2 (:REWRITE CDR-OF-UPDATE-NTH))
 (64 34 (:REWRITE DEFAULT-CDR))
 (34 20 (:REWRITE DEFAULT-CAR))
 (31 31 (:REWRITE USE-ALL-CONSP-2))
 (31 31 (:REWRITE USE-ALL-CONSP))
 (27 9 (:REWRITE ZP-OPEN))
 (26 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (16 11 (:REWRITE DEFAULT-<-2))
 (16 2 (:REWRITE CAR-OF-UPDATE-NTH))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11 (:REWRITE DEFAULT-<-1))
 )
(RENUMBERING-STOBJP-OF-UPDATE-RENUMBERINGI
 (9 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (6 1 (:DEFINITION RENUMBERING-ENTRIESP))
 (5 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (4 1 (:DEFINITION TRUE-LISTP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(RENUMBERING-LENGTH-OF-UPDATE-RENUMBERINGI
 (10 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (5 3 (:REWRITE DEFAULT-<-2))
 (5 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 )
(RENUMBERINGI-WHEN-NOT-NATP
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 )
(UPDATE-RENUMBERINGI-WHEN-NOT-NATP
 (8 4 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 )
(RENUMBERINGI-OF-UPDATE-RENUMBERINGI-SAME
 (12 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (7 3 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (6 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 )
(RENUMBERINGI-OF-UPDATE-RENUMBERINGI-DIFF
 (75 30 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (60 30 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (35 15 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (15 15 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(RENUMBERINGI-OF-UPDATE-RENUMBERINGI-SPLIT
 (37 29 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (29 29 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 )
(UPDATE-RENUMBERINGI-OF-UPDATE-RENUMBERINGI-SAME
 (9 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (5 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(UPDATE-RENUMBERINGI-OF-UPDATE-RENUMBERINGI-DIFF
 (80 20 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (50 20 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (40 20 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (20 20 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (10 10 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(UPDATE-RENUMBERINGI-OF-UPDATE-RENUMBERINGI-SPLIT
 (83 34 (:REWRITE DEFAULT-CDR))
 (46 23 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (35 23 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (23 23 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (18 12 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE USE-ALL-CONSP-2))
 (17 17 (:REWRITE USE-ALL-CONSP))
 (16 1 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-RENUMBERINGI-OF-UPDATE-RENUMBERINGI-SAME-VALUES
 (16 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (10 4 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE NTH-WHEN-ZP-CHEAP))
 )
(MAYBE-DARGP-OF-NTH-WHEN-RENUMBERING-ENTRIESP
 (12 6 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (9 9 (:REWRITE USE-ALL-CONSP-2))
 (9 9 (:REWRITE USE-ALL-CONSP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(MAYBE-DARGP-OF-RENUMBERINGI)
(RENUMBERING-ENTRIESP-OF-RESIZE-LIST
 (20 15 (:REWRITE DEFAULT-CDR))
 (16 14 (:REWRITE DEFAULT-CAR))
 (12 6 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (11 11 (:REWRITE USE-ALL-CONSP-2))
 (11 11 (:REWRITE USE-ALL-CONSP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (6 1 (:REWRITE CAR-OF-RESIZE-LIST))
 (5 2 (:REWRITE CONSP-OF-RESIZE-LIST))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (3 1 (:DEFINITION POSP))
 )
(RENUMBERING-STOBJP-OF-RESIZE-RENUMBERING
 (6 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (4 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (4 1 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (3 3 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(RENUMBERING-LENGTH-OF-RESIZE-RENUMBERING
 (6 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (3 1 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
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
(RENUMBERINGI-OF-RESIZE-RENUMBERING
 (12 7 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (12 7 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (10 8 (:REWRITE DEFAULT-<-2))
 (10 7 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (8 8 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 1 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 1 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION RESIZE-LIST))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1 1 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 )
(RESIZE-RENUMBERING-OF-UPDATE-RENUMBERINGI
 (16 6 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (14 2 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
 (12 4 (:REWRITE RESIZE-LIST-WHEN-NOT-CONSP))
 (11 1 (:REWRITE DEFAULT-CAR))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE USE-ALL-CONSP-2))
 (5 5 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 )
(RENUMBERING-STOBJP-OF-CREATE-RENUMBERING-STOBJ
 (1 1 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(NATP-OF-RENUMBERINGI
 (6 3 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (4 3 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION MYQUOTEP))
 (3 3 (:REWRITE USE-ALL-DARGP-2))
 (3 3 (:REWRITE USE-ALL-DARGP))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 )
(INTEGERP-OF-RENUMBERINGI
 (6 3 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (5 3 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (3 3 (:TYPE-PRESCRIPTION MYQUOTEP))
 (3 3 (:REWRITE USE-ALL-DARGP-2))
 (3 3 (:REWRITE USE-ALL-DARGP))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(EQUAL-OF-CAR-OF-RENUMBERINGI-AND-QUOTE
 (3 3 (:REWRITE USE-ALL-DARGP-2))
 (3 3 (:REWRITE USE-ALL-DARGP))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(MYQUOTEP-OF-RENUMBERINGI
 (3 3 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 )
(GOOD-RENUMBERING-STOBJ-AUX
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 )
(GOOD-RENUMBERING-STOBJ-AUX-MONOTONE
 (22 11 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (22 11 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (12 12 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (11 11 (:TYPE-PRESCRIPTION MYQUOTEP))
 (11 11 (:REWRITE USE-ALL-DARGP-2))
 (11 11 (:REWRITE USE-ALL-DARGP))
 (11 11 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (11 11 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (11 11 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(GOOD-RENUMBERING-STOBJ-AUX-OF-UPDATE-RENUMBERINGI-IRREL
 (28 14 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (28 14 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (16 16 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (14 14 (:TYPE-PRESCRIPTION MYQUOTEP))
 (14 14 (:REWRITE USE-ALL-DARGP-2))
 (14 14 (:REWRITE USE-ALL-DARGP))
 (14 14 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (14 14 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (14 14 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (10 10 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(RENUMBERINGI-WHEN-GOOD-RENUMBERING-STOBJ-AUX-IFF
 (1 1 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 )
(GOOD-RENUMBERING-STOBJ)
(GOOD-RENUMBERING-STOBJ-OF-IF)
(GOOD-RENUMBERING-STOBJ-MONOTONE
 (14 1 (:DEFINITION GOOD-RENUMBERING-STOBJ-AUX))
 (7 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:TYPE-PRESCRIPTION DARGP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 )
(GOOD-RENUMBERING-STOBJ-OF--1
 (1 1 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 )
(GOOD-RENUMBERING-STOBJ-AFTER-UPDATE-RENUMBERINGI
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (6 3 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:TYPE-PRESCRIPTION MYQUOTEP))
 (3 3 (:REWRITE USE-ALL-DARGP-2))
 (3 3 (:REWRITE USE-ALL-DARGP))
 (3 3 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE RENUMBERINGI-OF-UPDATE-RENUMBERINGI-DIFF))
 (1 1 (:REWRITE GOOD-RENUMBERING-STOBJ-MONOTONE))
 )
(RENUMBERINGI-WHEN-GOOD-RENUMBERING-STOBJ-IFF
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-AUX
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE
 (66 33 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (51 36 (:REWRITE DEFAULT-<-2))
 (51 36 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (33 33 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (33 33 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (33 33 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (32 32 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE DEFAULT-+-1))
 (30 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-OF-UPDATE-RENUMBERINGI-IRREL
 (16 8 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (14 14 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (8 8 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-OF-UPDATE-RENUMBERINGI
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (9 9 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (5 5 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (5 5 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE RENUMBERINGI-OF-UPDATE-RENUMBERINGI-DIFF))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-OF-UPDATE-RENUMBERINGI-GEN
 (22 11 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (15 15 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (11 11 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(<-OF-RENUMBERINGI-WHEN-BOUNDED-GOOD-RENUMBERING-STOBJ-AUX
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 (1 1 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ)
(BOUNDED-GOOD-RENUMBERING-STOBJ-FORWARD)
(BOUNDED-GOOD-RENUMBERING-STOBJ-FORWARD-TO-GOOD-RENUMBERING-STOBJ
 (17 9 (:REWRITE DEFAULT-<-2))
 (14 9 (:REWRITE DEFAULT-<-1))
 (14 7 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (12 6 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (12 6 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (11 9 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (10 10 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-MONO))
 (6 6 (:TYPE-PRESCRIPTION MYQUOTEP))
 (6 6 (:REWRITE USE-ALL-DARGP-2))
 (6 6 (:REWRITE USE-ALL-DARGP))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (6 6 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE GOOD-RENUMBERING-STOBJ-MONOTONE))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-OF-IF)
(BOUNDED-GOOD-RENUMBERING-STOBJ-MONOTONE
 (12 1 (:DEFINITION BOUNDED-GOOD-RENUMBERING-STOBJ-AUX))
 (9 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-OF--1
 (1 1 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-OF-UPDATE-RENUMBERINGI
 (37 2 (:DEFINITION BOUNDED-GOOD-RENUMBERING-STOBJ-AUX))
 (27 1 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-OF-UPDATE-RENUMBERINGI-GEN))
 (8 4 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (6 4 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (4 4 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (4 4 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (4 4 (:REWRITE DARGP-LESS-THAN-MONO))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-MONOTONE))
 )
(BOUNDED-GOOD-RENUMBERING-STOBJ-OF-UPDATE-RENUMBERINGI-GEN
 (12 1 (:DEFINITION BOUNDED-GOOD-RENUMBERING-STOBJ-AUX))
 (5 3 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-MONO))
 (2 2 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-MONOTONE))
 )
(<-OF-RENUMBERINGI-WHEN-BOUNDED-GOOD-RENUMBERING-STOBJ
 (5 1 (:REWRITE <-OF-RENUMBERINGI-WHEN-BOUNDED-GOOD-RENUMBERING-STOBJ-AUX))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 )
(RENUMBER-DARG-WITH-STOBJ$INLINE)
(DARGP-OF-RENUMBER-DARG-WITH-STOBJ
 (16 8 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (15 8 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (9 9 (:REWRITE USE-ALL-DARGP-2))
 (9 9 (:REWRITE USE-ALL-DARGP))
 (9 9 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (9 9 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(DARGP-LESS-THAN-OF-RENUMBER-DARG-WITH-STOBJ
 (11 6 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (6 6 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (6 6 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (6 6 (:REWRITE DARGP-LESS-THAN-MONO))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (5 3 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (4 4 (:REWRITE BOUNDED-GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (3 3 (:REWRITE USE-ALL-DARGP-2))
 (3 3 (:REWRITE USE-ALL-DARGP))
 (3 3 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE USE-ALL-CONSP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(NATP-OF-RENUMBER-DARG-WITH-STOBJ
 (20 10 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (15 10 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (11 11 (:REWRITE USE-ALL-DARGP-2))
 (11 11 (:REWRITE USE-ALL-DARGP))
 (11 11 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (11 11 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (10 10 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (10 5 (:REWRITE DEFAULT-<-2))
 (9 5 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE USE-ALL-CONSP-2))
 (8 8 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 )
(INTEGERP-OF-RENUMBER-DARG-WITH-STOBJ
 (20 10 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (16 10 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (11 11 (:REWRITE USE-ALL-DARGP-2))
 (11 11 (:REWRITE USE-ALL-DARGP))
 (11 11 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (11 11 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (10 10 (:REWRITE GOOD-RENUMBERING-STOBJ-AUX-MONOTONE))
 (10 5 (:REWRITE DEFAULT-<-2))
 (9 5 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE USE-ALL-CONSP-2))
 (8 8 (:REWRITE USE-ALL-CONSP))
 (5 5 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 )
(RENUMBER-DARGS-WITH-STOBJ
 (36 18 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (23 23 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (16 8 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (16 8 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION ALL-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE USE-ALL-CONSP-2))
 (8 8 (:REWRITE USE-ALL-CONSP))
 (8 6 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (6 1 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (5 1 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4 4 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (2 2 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(ALL-DARGP-OF-RENUMBER-DARGS-WITH-STOBJ
 (639 190 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (386 193 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (244 236 (:REWRITE DEFAULT-CDR))
 (220 220 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (193 193 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (189 189 (:REWRITE USE-ALL-CONSP-2))
 (189 189 (:REWRITE USE-ALL-CONSP))
 (146 82 (:REWRITE USE-ALL-DARGP))
 (145 139 (:REWRITE DEFAULT-CAR))
 (87 44 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (82 82 (:REWRITE USE-ALL-DARGP-2))
 (82 82 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (66 33 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (64 64 (:TYPE-PRESCRIPTION MEMBERP))
 (62 1 (:REWRITE GOOD-RENUMBERING-STOBJ-OF-IF))
 (58 58 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (42 21 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (42 21 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (32 32 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (32 32 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (23 23 (:TYPE-PRESCRIPTION ALL-CONSP))
 (14 2 (:REWRITE <-OF-LARGEST-NON-QUOTEP))
 (10 2 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (8 2 (:REWRITE DEFAULT-<-1))
 (8 1 (:LINEAR <=-OF--1-AND-LARGEST-NON-QUOTEP-LINEAR))
 (5 1 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4 4 (:TYPE-PRESCRIPTION BOUNDED-DARG-LISTP))
 (4 4 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (4 1 (:REWRITE LARGEST-NON-QUOTEP-BOUND))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(BOUNDED-DARG-LISTP-OF-RENUMBER-DARGS-WITH-STOBJ
 (1613 820 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (1491 75 (:REWRITE <-OF-LARGEST-NON-QUOTEP))
 (1400 93 (:REWRITE ALL-DARGP-OF-CDR))
 (898 898 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (798 114 (:REWRITE BOUNDED-DARG-LISTP-OF-CDR))
 (445 47 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (434 217 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (364 165 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (345 345 (:TYPE-PRESCRIPTION ALL-CONSP))
 (343 137 (:REWRITE DEFAULT-<-1))
 (334 167 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (334 167 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (332 166 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (322 322 (:REWRITE USE-ALL-CONSP-2))
 (322 322 (:REWRITE USE-ALL-CONSP))
 (309 301 (:REWRITE DEFAULT-CDR))
 (250 226 (:REWRITE DEFAULT-CAR))
 (210 42 (:REWRITE ALL-CONSP-OF-CDR))
 (166 166 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (140 137 (:REWRITE DEFAULT-<-2))
 (120 100 (:REWRITE USE-ALL-DARGP))
 (100 100 (:REWRITE USE-ALL-DARGP-2))
 (100 100 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (94 47 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (89 89 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (89 89 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (86 45 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (65 65 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (62 62 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (48 48 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (48 48 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (48 48 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (48 48 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (48 3 (:REWRITE BOUNDED-DARG-LISTP-OF-0))
 (47 47 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (21 3 (:DEFINITION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION MEMBERP))
 (16 8 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (16 1 (:REWRITE <=-OF-LARGEST-NON-QUOTEP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (9 3 (:REWRITE ALL-MYQUOTEP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (8 8 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (8 8 (:REWRITE DARGP-LESS-THAN-MONO))
 (6 3 (:REWRITE ALL-MYQUOTEP-OF-CDR-CHEAP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
