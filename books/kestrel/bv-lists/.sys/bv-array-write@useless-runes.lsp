(BV-ARRAY-WRITE)
(TRUE-LISTP-OF-BV-ARRAY-WRITE)
(ALL-INTEGERP-OF-BV-ARRAY-WRITE)
(BV-ARRAY-WRITE-NORMAL-CASE
 (427 5 (:DEFINITION UPDATE-NTH))
 (242 4 (:REWRITE CDR-OF-BVCHOP-LIST))
 (130 9 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (101 33 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (89 29 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (88 2 (:REWRITE CAR-OF-BVCHOP-LIST))
 (80 7 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (62 9 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (58 58 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (57 3 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (55 2 (:REWRITE CDR-OF-TRUE-LIST-FIX))
 (48 13 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (48 3 (:DEFINITION TRUE-LISTP))
 (47 17 (:REWRITE DEFAULT-CDR))
 (45 9 (:REWRITE LEN-OF-CDR))
 (35 6 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (33 33 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (32 12 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (31 31 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (31 31 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (27 25 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (26 26 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (26 21 (:REWRITE DEFAULT-<-1))
 (25 21 (:REWRITE DEFAULT-<-2))
 (22 7 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 4 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (15 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE DEFAULT-CAR))
 (13 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (12 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (12 2 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (12 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 2 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (7 7 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (6 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TRUE-LIST-FIX))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (5 5 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 2 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (4 1 (:REWRITE CAR-OF-TRUE-LIST-FIX))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (1 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(LEN-OF-BV-ARRAY-WRITE
 (404 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (321 3 (:DEFINITION UPDATE-NTH))
 (202 10 (:REWRITE TAKE-DOES-NOTHING))
 (185 19 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (164 4 (:REWRITE CDR-OF-TAKE))
 (138 6 (:DEFINITION EXPT))
 (128 16 (:REWRITE BVCHOP-IDENTITY))
 (111 72 (:REWRITE DEFAULT-<-2))
 (108 72 (:REWRITE DEFAULT-<-1))
 (105 14 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (90 6 (:REWRITE EQUAL-OF-LEN-AND-0))
 (84 42 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (84 4 (:REWRITE LEN-OF-CDR))
 (78 32 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (67 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (64 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (60 6 (:REWRITE DEFAULT-CDR))
 (60 3 (:REWRITE ZP-OPEN))
 (54 9 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (52 13 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (42 6 (:REWRITE ZIP-OPEN))
 (41 27 (:REWRITE DEFAULT-+-2))
 (30 30 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (30 3 (:REWRITE DEFAULT-CAR))
 (28 14 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (28 14 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (28 14 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (27 27 (:REWRITE DEFAULT-+-1))
 (22 2 (:REWRITE CAR-OF-TAKE-STRONG))
 (19 19 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (18 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 6 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (18 6 (:REWRITE DEFAULT-*-2))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (16 16 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (16 16 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (15 15 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (15 15 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (14 14 (:TYPE-PRESCRIPTION POSP))
 (14 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (14 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (10 10 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (9 9 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (9 9 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE BVCHOP-BOUND))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (5 5 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (5 5 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (4 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 )
(CONSP-OF-BV-ARRAY-WRITE
 (407 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (404 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (321 3 (:DEFINITION UPDATE-NTH))
 (227 18 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (164 4 (:REWRITE CDR-OF-TAKE))
 (162 9 (:REWRITE TAKE-DOES-NOTHING))
 (143 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (129 129 (:TYPE-PRESCRIPTION LEN))
 (92 4 (:DEFINITION EXPT))
 (87 56 (:REWRITE DEFAULT-<-2))
 (85 56 (:REWRITE DEFAULT-<-1))
 (84 4 (:REWRITE LEN-OF-CDR))
 (83 25 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (82 10 (:REWRITE BVCHOP-IDENTITY))
 (81 39 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (73 10 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (67 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (64 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (61 4 (:REWRITE ZP-OPEN))
 (60 6 (:REWRITE DEFAULT-CDR))
 (56 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 (36 9 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (31 21 (:REWRITE DEFAULT-+-2))
 (30 10 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (30 3 (:REWRITE DEFAULT-CAR))
 (28 4 (:REWRITE ZIP-OPEN))
 (22 2 (:REWRITE CAR-OF-TAKE-STRONG))
 (22 1 (:REWRITE LEN-OF-BVCHOP-LIST))
 (21 21 (:REWRITE DEFAULT-+-1))
 (20 10 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (20 10 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (20 10 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 18 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 4 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (12 4 (:REWRITE DEFAULT-*-2))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:TYPE-PRESCRIPTION POSP))
 (10 10 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (10 10 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (10 10 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (10 10 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (8 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (5 5 (:REWRITE BVCHOP-BOUND))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (4 1 (:REWRITE LEN-OF-TAKE))
 (4 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 )
(ALL-UNSIGNED-BYTE-P-OF-BV-ARRAY-WRITE-SAME
 (68 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (58 1 (:LINEAR BVCHOP-UPPER-BOUND))
 (54 4 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (50 2 (:REWRITE TAKE-DOES-NOTHING))
 (48 48 (:TYPE-PRESCRIPTION CEILING-OF-LG))
 (46 2 (:DEFINITION EXPT))
 (42 7 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (38 6 (:REWRITE BVCHOP-IDENTITY))
 (34 26 (:REWRITE DEFAULT-<-2))
 (34 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (32 26 (:REWRITE DEFAULT-<-1))
 (26 26 (:TYPE-PRESCRIPTION LEN))
 (25 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (14 2 (:REWRITE ZIP-OPEN))
 (13 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (12 3 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (10 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8 5 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 2 (:REWRITE CONSP-OF-UPDATE-NTH2))
 (7 7 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (7 7 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (6 5 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 2 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (6 2 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 2 (:DEFINITION POSP))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (5 5 (:TYPE-PRESCRIPTION UPDATE-NTH2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (1 1 (:REWRITE LEN-OF-UPDATE-NTH2))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-BOUND))
 (1 1 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 )
(ALL-UNSIGNED-BYTE-P-OF-BV-ARRAY-WRITE
 (68 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (58 1 (:LINEAR BVCHOP-UPPER-BOUND))
 (54 4 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (50 2 (:REWRITE TAKE-DOES-NOTHING))
 (48 48 (:TYPE-PRESCRIPTION CEILING-OF-LG))
 (46 2 (:DEFINITION EXPT))
 (42 7 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (38 30 (:REWRITE DEFAULT-<-2))
 (38 6 (:REWRITE BVCHOP-IDENTITY))
 (36 30 (:REWRITE DEFAULT-<-1))
 (34 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (26 26 (:TYPE-PRESCRIPTION LEN))
 (25 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (14 2 (:REWRITE ZIP-OPEN))
 (13 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (12 3 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (10 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8 5 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 2 (:REWRITE CONSP-OF-UPDATE-NTH2))
 (7 7 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (7 7 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (6 5 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 2 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (6 2 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 2 (:DEFINITION POSP))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (6 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (5 5 (:TYPE-PRESCRIPTION UPDATE-NTH2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (1 1 (:REWRITE LEN-OF-UPDATE-NTH2))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-BOUND))
 (1 1 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 )
(BV-ARRAY-WRITE-IFF
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(EQUAL-OF-NIL-AND-BV-ARRAY-WRITE
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(EQUAL-OF-BV-ARRAY-WRITE-AND-NIL
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BV-ARRAY-WRITE-OF-0)
(BV-ARRAY-WRITE-OPENER
 (16 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (13 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (12 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (10 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (7 6 (:REWRITE DEFAULT-<-1))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (6 6 (:TYPE-PRESCRIPTION UPDATE-NTH2))
 (6 6 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE DEFAULT-<-2))
 (5 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE LEN-OF-UPDATE-NTH2))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP
 (193 9 (:REWRITE TAKE-DOES-NOTHING))
 (96 5 (:REWRITE LEN-OF-CDR))
 (95 95 (:TYPE-PRESCRIPTION LEN))
 (95 7 (:REWRITE EQUAL-OF-LEN-AND-0))
 (92 13 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (61 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (41 2 (:REWRITE LEN-OF-CONS))
 (27 4 (:REWRITE BVCHOP-IDENTITY))
 (26 25 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (26 19 (:REWRITE DEFAULT-<-2))
 (22 19 (:REWRITE DEFAULT-<-1))
 (21 3 (:REWRITE DEFAULT-CDR))
 (17 10 (:REWRITE DEFAULT-+-2))
 (16 11 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (13 13 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (11 11 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (11 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (7 2 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (7 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (5 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION CEILING-OF-LG))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BV-ARRAY-WRITE-WHEN-INDEX-IS-TOO-LARGE
 (46 2 (:DEFINITION EXPT))
 (45 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER-2))
 (36 4 (:REWRITE BVCHOP-IDENTITY))
 (36 4 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (32 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (27 20 (:REWRITE DEFAULT-<-2))
 (27 20 (:REWRITE DEFAULT-<-1))
 (22 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (22 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (20 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (16 4 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (15 2 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (14 2 (:REWRITE ZIP-OPEN))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (12 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 3 (:REWRITE TAKE-DOES-NOTHING))
 (10 2 (:REWRITE CONSP-OF-TAKE))
 (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (8 5 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (8 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (7 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-TAKE-2))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (6 2 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (4 4 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (4 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 1 (:REWRITE LEN-OF-TAKE))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (3 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-BOUND))
 (1 1 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 )
(BV-ARRAY-WRITE-OF-1-ARG2
 (36 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CONS))
 (21 1 (:REWRITE LEN-OF-CDR))
 (20 20 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (18 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (14 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (13 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (11 3 (:REWRITE BVCHOP-IDENTITY))
 (10 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (10 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (10 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CONS))
 (10 1 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (5 3 (:REWRITE DEFAULT-<-2))
 (5 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (5 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 3 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:DEFINITION NOT))
 )
(BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP
 (50 2 (:REWRITE TAKE-DOES-NOTHING))
 (34 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (22 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (10 2 (:REWRITE BVCHOP-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 )
(EQUAL-OF-BV-ARRAY-WRITE-OF-1
 (87 19 (:REWRITE BVCHOP-IDENTITY))
 (70 19 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (66 3 (:DEFINITION EXPT))
 (50 50 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (46 28 (:REWRITE DEFAULT-<-2))
 (41 41 (:TYPE-PRESCRIPTION NATP))
 (38 19 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (38 19 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (38 19 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (36 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CONS))
 (32 28 (:REWRITE DEFAULT-<-1))
 (26 4 (:DEFINITION TRUE-LISTP))
 (25 25 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (25 25 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:TYPE-PRESCRIPTION POSP))
 (19 19 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (19 19 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (19 19 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (19 19 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (19 19 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (18 6 (:REWRITE DEFAULT-*-2))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (17 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (17 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (16 14 (:REWRITE DEFAULT-+-2))
 (15 9 (:REWRITE DEFAULT-CAR))
 (15 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (14 14 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (12 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (10 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CONS))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9 6 (:REWRITE DEFAULT-CDR))
 (9 3 (:DEFINITION NATP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (4 4 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (4 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (3 3 (:REWRITE ZIP-OPEN))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (1 1 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 )
(EQUAL-OF-BV-ARRAY-WRITE-OF-1-CONSTANT-VERSION
 (87 19 (:REWRITE BVCHOP-IDENTITY))
 (70 19 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (66 3 (:DEFINITION EXPT))
 (50 50 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (46 28 (:REWRITE DEFAULT-<-2))
 (41 41 (:TYPE-PRESCRIPTION NATP))
 (38 19 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (38 19 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (38 19 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (36 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CONS))
 (32 28 (:REWRITE DEFAULT-<-1))
 (26 4 (:DEFINITION TRUE-LISTP))
 (25 25 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (25 25 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:TYPE-PRESCRIPTION POSP))
 (19 19 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (19 19 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (19 19 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (19 19 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (19 19 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (18 6 (:REWRITE DEFAULT-*-2))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (17 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (17 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (16 14 (:REWRITE DEFAULT-+-2))
 (15 9 (:REWRITE DEFAULT-CAR))
 (15 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (14 14 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (12 1 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (10 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CONS))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9 6 (:REWRITE DEFAULT-CDR))
 (9 3 (:DEFINITION NATP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (4 4 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (4 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (3 3 (:REWRITE ZIP-OPEN))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (1 1 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 )
(UPDATE-NTH2-BECOMES-BV-ARRAY-WRITE
 (110 5 (:DEFINITION UPDATE-NTH))
 (84 21 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (72 12 (:REWRITE DEFAULT-CDR))
 (36 6 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (25 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (22 1 (:DEFINITION MEMBER-EQUAL))
 (21 21 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (19 14 (:REWRITE DEFAULT-<-2))
 (18 14 (:REWRITE DEFAULT-<-1))
 (12 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (12 1 (:DEFINITION TRUE-LISTP))
 (8 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (2 2 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (2 1 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(UPDATE-NTH-BECOMES-BV-ARRAY-WRITE
 (88 4 (:DEFINITION UPDATE-NTH))
 (72 18 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (60 10 (:REWRITE DEFAULT-CDR))
 (30 5 (:REWRITE DEFAULT-CAR))
 (25 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (22 1 (:DEFINITION MEMBER-EQUAL))
 (21 21 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (18 18 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (12 1 (:DEFINITION TRUE-LISTP))
 (11 8 (:REWRITE DEFAULT-<-2))
 (10 8 (:REWRITE DEFAULT-<-1))
 (8 1 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (2 1 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE UPDATE-NTH2-TOO-HIGH))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(BV-ARRAY-WRITE-OF-TRUE-LIST-FIX
 (583 5 (:DEFINITION UPDATE-NTH))
 (404 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (335 35 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (280 16 (:REWRITE TAKE-DOES-NOTHING))
 (246 6 (:REWRITE CDR-OF-TAKE))
 (235 235 (:TYPE-PRESCRIPTION LEN))
 (152 8 (:REWRITE LEN-OF-CDR))
 (144 6 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (130 10 (:REWRITE EQUAL-OF-LEN-AND-0))
 (126 6 (:DEFINITION TRUE-LISTP))
 (106 16 (:REWRITE DEFAULT-CDR))
 (100 5 (:REWRITE ZP-OPEN))
 (99 56 (:REWRITE DEFAULT-<-2))
 (92 42 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (90 56 (:REWRITE DEFAULT-<-1))
 (88 2 (:REWRITE CDR-OF-TRUE-LIST-FIX))
 (87 67 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (79 79 (:TYPE-PRESCRIPTION CEILING-OF-LG))
 (68 12 (:REWRITE BVCHOP-IDENTITY))
 (68 2 (:REWRITE BVCHOP-LIST-WHEN-UNSIGNED-BYTE-LISTP))
 (68 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (64 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (58 1 (:LINEAR BVCHOP-UPPER-BOUND))
 (50 8 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (50 5 (:REWRITE DEFAULT-CAR))
 (48 8 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (46 2 (:DEFINITION EXPT))
 (35 35 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (35 24 (:REWRITE DEFAULT-+-2))
 (33 3 (:REWRITE CAR-OF-TAKE-STRONG))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:REWRITE DEFAULT-+-1))
 (24 6 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (20 20 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (16 16 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (16 8 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (16 8 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (16 8 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (14 2 (:REWRITE ZIP-OPEN))
 (12 12 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (12 12 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (11 1 (:REWRITE CAR-OF-TRUE-LIST-FIX))
 (10 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 (8 8 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (8 8 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (8 8 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (8 8 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (7 7 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING-BETTER))
 (7 2 (:REWRITE BVCHOP-LIST-DOES-NOTHING))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 6 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (6 2 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (6 2 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE BVCHOP-BOUND))
 (5 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NEGATIVE))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 2 (:REWRITE BVCHOP-LIST-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 )
