(UNSIGNED-BYTE-LISTP-REWRITE
 (52 52 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE DEFAULT-CAR))
 (35 31 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (26 8 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (20 20 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (18 6 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (7 7 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP)
(UNSIGNED-BYTE-LISTP-FORWARD-TO-ALL-UNSIGNED-BYTE-P
 (82 15 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (52 9 (:DEFINITION MEMBER-EQUAL))
 (33 33 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (22 22 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE DEFAULT-CDR))
 (16 12 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (15 15 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (14 11 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (10 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (10 6 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(UNSIGNED-BYTE-LISTP-FORWARD-TO-TRUE-LISTP
 (15 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (15 3 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (12 12 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(NATP-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-FORWARD
 (35 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (35 7 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (28 28 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (18 18 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (11 11 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (11 11 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE DEFAULT-CDR))
 (7 4 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (3 3 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UNSIGNED-BYTE-LISTP-OF-CDR
 (5 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(UNSIGNED-BYTE-LISTP-OF-CONS
 (10 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (10 2 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (10 2 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (8 8 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (4 4 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(UNSIGNED-BYTE-LISTP-OF-APPEND
 (288 35 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (253 35 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (178 178 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (165 18 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-APPEND))
 (148 79 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (127 127 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (114 107 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (108 20 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (79 79 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (69 69 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (50 50 (:REWRITE DEFAULT-CDR))
 (47 47 (:REWRITE DEFAULT-CAR))
 (42 14 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (35 35 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (35 35 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 )
(UNSIGNED-BYTE-LISTP-OF-REVAPPEND
 (306 36 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (222 36 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (176 176 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (170 90 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (120 88 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (108 108 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (108 20 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (90 90 (:TYPE-PRESCRIPTION REVAPPEND))
 (84 20 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-REVAPPEND))
 (80 80 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (64 52 (:REWRITE DEFAULT-CDR))
 (60 48 (:REWRITE DEFAULT-CAR))
 (44 12 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (36 36 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (36 36 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 )
(UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2
 (15 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (15 3 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (12 12 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (5 1 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (4 4 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (3 3 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(UNSIGNED-BYTE-LISTP-OF-NTHCDR
 (64 14 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (32 32 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (27 26 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (23 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (19 19 (:REWRITE DEFAULT-CAR))
 (19 10 (:REWRITE ZP-OPEN))
 (17 17 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (17 17 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (12 12 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTHCDR-LONGER))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (5 1 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(UNSIGNED-BYTE-LISTP-OF-TAKE-2
 (339 47 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (275 47 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (194 194 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (140 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-IF))
 (116 4 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CONS))
 (113 99 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (107 107 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (100 18 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (57 57 (:REWRITE DEFAULT-CDR))
 (56 16 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (53 53 (:REWRITE DEFAULT-CAR))
 (53 37 (:REWRITE DEFAULT-<-1))
 (49 49 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (49 49 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (41 26 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE DEFAULT-+-1))
 (10 7 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NIL))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(UNSIGNED-BYTE-LISTP-OF-BUTLAST
 (558 14 (:DEFINITION UNSIGNED-BYTE-LISTP))
 (174 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-IF))
 (148 14 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (148 14 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (128 34 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (110 22 (:DEFINITION LEN))
 (90 13 (:DEFINITION TAKE))
 (70 14 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (70 14 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (68 68 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (67 45 (:REWRITE DEFAULT-+-2))
 (49 49 (:REWRITE DEFAULT-CDR))
 (45 45 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (38 38 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (34 26 (:REWRITE DEFAULT-<-2))
 (30 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TAKE))
 (29 26 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE ZP-OPEN))
 (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (14 14 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (14 14 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NIL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UNSIGNED-BYTE-LISTP-OF-TRUE-LIST-FIX
 (54 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (49 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (34 34 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (31 6 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX))
 (23 23 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (18 17 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (10 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 )
(INTEGERP-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP
 (42 26 (:REWRITE DEFAULT-<-2))
 (40 6 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (36 20 (:REWRITE DEFAULT-+-2))
 (26 26 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-+-1))
 (18 18 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 2 (:REWRITE ALL-INTEGERP-OF-CDR))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (8 8 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE ZP-OPEN))
 (4 2 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP
 (28 8 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (16 16 (:REWRITE DEFAULT-CAR))
 (16 2 (:DEFINITION MEMBER-EQUAL))
 (12 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (10 2 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 8 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP
 (29 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (18 18 (:REWRITE DEFAULT-CAR))
 (18 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (16 2 (:DEFINITION MEMBER-EQUAL))
 (15 3 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (14 11 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (12 12 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (11 11 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (9 8 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(UNSIGNED-BYTE-P-OF-NTH-WHEN-UNSIGNED-BYTE-LISTP-2
 (95 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (45 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (45 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (26 17 (:REWRITE DEFAULT-<-2))
 (23 14 (:REWRITE DEFAULT-+-2))
 (20 4 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (17 17 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (17 17 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (17 17 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (14 14 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (3 1 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 )
(ALL-INTEGERP-WHEN-UNSIGNED-BYTE-LISTP
 (183 19 (:REWRITE UNSIGNED-BYTE-LISTP-OF-CDR))
 (118 19 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (98 19 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (68 68 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (40 40 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (34 34 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (34 34 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (34 34 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (28 8 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (20 20 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (20 20 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (20 20 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (11 11 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-INTEGERP-OF-CDR))
 )
