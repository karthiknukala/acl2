(MAKE-BLOCKS
 (36 9 (:DEFINITION NTH))
 (25 1 (:REWRITE NON-NIL-NTH))
 (20 6 (:LINEAR NON-NIL-NTH))
 (19 12 (:REWRITE DEFAULT-+-2))
 (13 12 (:REWRITE DEFAULT-+-1))
 (12 1 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE MEMBER-OF-A-NAT-LIST))
 )
(MAKE-BLOCKS-CORRECTNESS-5
 (162 12 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (108 6 (:DEFINITION MAKE-CHARACTER-LIST))
 (102 6 (:DEFINITION TAKE))
 (75 39 (:REWRITE DEFAULT-CDR))
 (54 54 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (36 18 (:REWRITE DEFAULT-CAR))
 (34 17 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE CONSP-OF-TAKE))
 (24 22 (:LINEAR NON-NIL-NTH))
 (17 17 (:REWRITE DEFAULT-+-1))
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (6 3 (:DEFINITION NTHCDR))
 (4 2 (:DEFINITION NTH))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 1 (:REWRITE NON-NIL-NTH))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(BLOCK-LISTP)
(MAKE-BLOCKS-CORRECTNESS-2
 (84 6 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (83 39 (:REWRITE DEFAULT-CDR))
 (66 12 (:DEFINITION LEN))
 (61 23 (:REWRITE DEFAULT-CAR))
 (60 60 (:TYPE-PRESCRIPTION LEN))
 (60 9 (:REWRITE MAKE-BLOCKS-CORRECTNESS-5 . 1))
 (54 3 (:DEFINITION MAKE-CHARACTER-LIST))
 (51 3 (:DEFINITION TAKE))
 (48 3 (:REWRITE CONSP-OF-NTHCDR))
 (27 27 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (26 14 (:REWRITE DEFAULT-+-2))
 (24 14 (:LINEAR NON-NIL-NTH))
 (16 6 (:DEFINITION NTH))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE CONSP-OF-TAKE))
 (9 3 (:REWRITE NON-NIL-NTH))
 (4 3 (:REWRITE DEFAULT-<-2))
 (4 2 (:DEFINITION NTHCDR))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(BLOCK-LISTP-CORRECTNESS-1
 (36 4 (:REWRITE TRUE-LISTP-WHEN-STRING-LIST))
 (24 4 (:DEFINITION STRING-LISTP))
 (22 2 (:DEFINITION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION STRING-LISTP))
 (15 3 (:DEFINITION LEN))
 (14 14 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-CAR))
 (9 3 (:DEFINITION CHARACTER-LISTP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(BLOCK-LISTP-CORRECTNESS-2
 (149 128 (:REWRITE DEFAULT-CAR))
 (120 114 (:REWRITE DEFAULT-CDR))
 (106 53 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (100 14 (:REWRITE TRUE-LISTP-WHEN-STRING-LIST))
 (64 32 (:REWRITE DEFAULT-+-2))
 (63 14 (:DEFINITION STRING-LISTP))
 (53 53 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION STRING-LISTP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (5 3 (:LINEAR NON-NIL-NTH))
 (2 1 (:DEFINITION NTH))
 )
(FEASIBLE-FILE-LENGTH-P)
(UNMAKE-BLOCKS
 (290 166 (:REWRITE DEFAULT-+-2))
 (240 31 (:LINEAR NON-NIL-NTH))
 (210 210 (:REWRITE DEFAULT-CDR))
 (209 67 (:DEFINITION NTH))
 (166 166 (:REWRITE DEFAULT-+-1))
 (100 50 (:REWRITE DEFAULT-*-2))
 (97 97 (:REWRITE DEFAULT-CAR))
 (89 55 (:REWRITE DEFAULT-<-1))
 (72 8 (:REWRITE TRUE-LISTP-WHEN-STRING-LIST))
 (55 55 (:REWRITE DEFAULT-<-2))
 (50 50 (:REWRITE DEFAULT-*-1))
 (48 8 (:DEFINITION STRING-LISTP))
 (44 4 (:DEFINITION TRUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION STRING-LISTP))
 (21 21 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (7 7 (:REWRITE ZP-OPEN))
 )
(UNMAKE-BLOCKS-CORRECTNESS-1
 (520 62 (:LINEAR NON-NIL-NTH))
 (458 127 (:DEFINITION NTH))
 (445 445 (:REWRITE DEFAULT-CDR))
 (431 305 (:REWRITE DEFAULT-+-2))
 (401 30 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (305 305 (:REWRITE DEFAULT-+-1))
 (251 251 (:REWRITE DEFAULT-CAR))
 (115 84 (:REWRITE DEFAULT-<-1))
 (90 30 (:DEFINITION BINARY-APPEND))
 (90 10 (:REWRITE TRUE-LISTP-WHEN-STRING-LIST))
 (84 84 (:REWRITE DEFAULT-<-2))
 (84 43 (:REWRITE DEFAULT-*-2))
 (70 5 (:DEFINITION TRUE-LISTP))
 (60 10 (:DEFINITION STRING-LISTP))
 (50 50 (:TYPE-PRESCRIPTION STRING-LISTP))
 (44 44 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (43 43 (:REWRITE DEFAULT-*-1))
 (31 25 (:REWRITE ZP-OPEN))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UNMAKE-BLOCKS-CORRECTNESS-2
 (715 87 (:LINEAR NON-NIL-NTH))
 (628 123 (:DEFINITION NTH))
 (557 38 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (422 280 (:REWRITE DEFAULT-+-2))
 (365 365 (:REWRITE DEFAULT-CDR))
 (280 280 (:REWRITE DEFAULT-+-1))
 (187 187 (:REWRITE DEFAULT-CAR))
 (111 37 (:DEFINITION BINARY-APPEND))
 (75 25 (:DEFINITION CHARACTER-LISTP))
 (70 35 (:REWRITE DEFAULT-*-2))
 (66 54 (:REWRITE ZP-OPEN))
 (65 43 (:REWRITE DEFAULT-<-1))
 (43 43 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE DEFAULT-*-1))
 (16 16 (:REWRITE MEMBER-OF-A-NAT-LIST))
 )
(UNMAKE-MAKE-BLOCKS-LEMMA-1
 (55 38 (:REWRITE DEFAULT-+-2))
 (55 29 (:REWRITE DEFAULT-CDR))
 (38 38 (:REWRITE DEFAULT-+-1))
 (25 3 (:REWRITE NON-NIL-NTH))
 (24 18 (:REWRITE DEFAULT-<-2))
 (22 2 (:DEFINITION NTH))
 (18 18 (:REWRITE DEFAULT-<-1))
 (14 1 (:DEFINITION NTHCDR))
 (13 4 (:REWRITE ZP-OPEN))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE MEMBER-OF-A-NAT-LIST))
 )
(UNMAKE-MAKE-BLOCKS
 (919 12 (:DEFINITION TAKE))
 (704 107 (:DEFINITION NTH))
 (616 23 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (591 81 (:LINEAR NON-NIL-NTH))
 (463 85 (:DEFINITION LEN))
 (374 250 (:REWRITE DEFAULT-CDR))
 (313 217 (:REWRITE DEFAULT-+-2))
 (247 51 (:REWRITE NON-NIL-NTH))
 (230 58 (:REWRITE DEFAULT-CAR))
 (222 217 (:REWRITE DEFAULT-+-1))
 (200 5 (:DEFINITION MAKE-CHARACTER-LIST))
 (153 120 (:REWRITE DEFAULT-<-2))
 (150 32 (:REWRITE ZP-OPEN))
 (147 120 (:REWRITE DEFAULT-<-1))
 (96 30 (:REWRITE FOLD-CONSTS-IN-+))
 (73 25 (:REWRITE TAKE-WHEN-ATOM))
 (46 8 (:DEFINITION BINARY-APPEND))
 (26 7 (:DEFINITION NTHCDR))
 (24 24 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (23 23 (:REWRITE CONSP-OF-TAKE))
 (4 2 (:REWRITE LEN-OF-MAKE-CHARACTER-LIST))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE CHARACTER-LISTP-OF-NTHCDR))
 (1 1 (:DEFINITION NATP))
 )
(MAKE-BLOCKS-CORRECTNESS-1
 (264 11 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (189 117 (:REWRITE DEFAULT-+-2))
 (166 12 (:REWRITE MAKE-BLOCKS-CORRECTNESS-5 . 1))
 (122 117 (:REWRITE DEFAULT-+-1))
 (105 20 (:REWRITE NON-NIL-NTH))
 (72 4 (:DEFINITION MAKE-CHARACTER-LIST))
 (56 40 (:REWRITE DEFAULT-<-2))
 (56 12 (:REWRITE ZP-OPEN))
 (49 40 (:REWRITE DEFAULT-<-1))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (20 10 (:REWRITE DEFAULT-*-2))
 (16 16 (:REWRITE CONSP-OF-TAKE))
 (10 10 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE MEMBER-OF-A-NAT-LIST))
 )
(MAKE-BLOCKS-CORRECTNESS-3
 (66 4 (:REWRITE NON-NIL-NTH))
 (45 6 (:DEFINITION LEN))
 (30 2 (:DEFINITION NTH))
 (24 2 (:DEFINITION NATP))
 (21 12 (:REWRITE DEFAULT-+-2))
 (19 10 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE ZP-OPEN))
 (14 8 (:REWRITE DEFAULT-<-2))
 (14 8 (:REWRITE DEFAULT-<-1))
 (13 12 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (9 9 (:TYPE-PRESCRIPTION MAKE-BLOCKS))
 (6 6 (:REWRITE MAKE-BLOCKS-CORRECTNESS-5 . 1))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:LINEAR NON-NIL-NTH))
 )
(NTHCDR-*BLOCKSIZE*-INDUCTION-2
 (109 2 (:DEFINITION ACL2-COUNT))
 (29 2 (:REWRITE UNMAKE-MAKE-BLOCKS-LEMMA-1))
 (28 10 (:REWRITE DEFAULT-CDR))
 (26 13 (:REWRITE DEFAULT-+-2))
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (17 13 (:REWRITE DEFAULT-+-1))
 (15 3 (:DEFINITION LEN))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 4 (:DEFINITION NTH))
 (10 2 (:DEFINITION INTEGER-ABS))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 1 (:DEFINITION LENGTH))
 (6 2 (:REWRITE NON-NIL-NTH))
 (5 4 (:REWRITE DEFAULT-<-2))
 (5 1 (:LINEAR NON-NIL-NTH))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 1 (:DEFINITION NTHCDR))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:REWRITE CAR-OF-NTHCDR))
 (2 2 (:REWRITE NTHCDR-WHEN-ZP))
 (2 2 (:REWRITE NTHCDR-WHEN-ATOM))
 (2 2 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE OPEN-SMALL-NTHCDR))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MAKE-BLOCKS-CORRECTNESS-4
 (468 24 (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))
 (460 12 (:DEFINITION TAKE))
 (355 147 (:REWRITE DEFAULT-CDR))
 (216 12 (:DEFINITION MAKE-CHARACTER-LIST))
 (200 20 (:REWRITE UNMAKE-MAKE-BLOCKS-LEMMA-1))
 (193 53 (:DEFINITION NTH))
 (184 43 (:LINEAR NON-NIL-NTH))
 (148 74 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (147 88 (:REWRITE DEFAULT-+-2))
 (108 108 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (90 88 (:REWRITE DEFAULT-+-1))
 (84 12 (:REWRITE MAKE-BLOCKS-CORRECTNESS-5 . 1))
 (74 74 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (66 30 (:REWRITE DEFAULT-CAR))
 (64 16 (:DEFINITION NTHCDR))
 (60 20 (:REWRITE NON-NIL-NTH))
 (48 48 (:REWRITE CONSP-OF-TAKE))
 (48 6 (:REWRITE NTHCDR-OF-NTHCDR))
 (38 28 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE NTHCDR-WHEN-ZP))
 (32 32 (:REWRITE NTHCDR-WHEN-ATOM))
 (30 28 (:REWRITE DEFAULT-<-1))
 (18 6 (:REWRITE CAR-OF-NTHCDR))
 (16 16 (:REWRITE OPEN-SMALL-NTHCDR))
 (8 8 (:REWRITE MEMBER-OF-A-NAT-LIST))
 )
(LEN-OF-MAKE-UNMAKE
 (5590 269 (:LINEAR NON-NIL-NTH))
 (5329 651 (:DEFINITION NTH))
 (2455 123 (:REWRITE UNMAKE-BLOCKS-CORRECTNESS-2))
 (1831 245 (:REWRITE MAKE-BLOCKS-CORRECTNESS-5 . 1))
 (1551 1060 (:REWRITE DEFAULT-+-2))
 (1060 1060 (:REWRITE DEFAULT-+-1))
 (518 259 (:REWRITE DEFAULT-*-2))
 (461 356 (:REWRITE CONSP-OF-TAKE))
 (284 218 (:REWRITE DEFAULT-<-1))
 (259 259 (:REWRITE DEFAULT-*-1))
 (218 218 (:REWRITE DEFAULT-<-2))
 (146 80 (:REWRITE ZP-OPEN))
 (144 16 (:REWRITE TRUE-LISTP-WHEN-STRING-LIST))
 (112 8 (:DEFINITION TRUE-LISTP))
 (96 16 (:DEFINITION STRING-LISTP))
 (92 92 (:REWRITE MEMBER-OF-A-NAT-LIST))
 (88 4 (:REWRITE LEN-OF-BINARY-APPEND))
 (80 80 (:TYPE-PRESCRIPTION STRING-LISTP))
 (68 4 (:REWRITE NTH-ADD1))
 (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION NATP))
 (36 2 (:REWRITE LEN-OF-NTHCDR))
 (19 19 (:REWRITE MAKE-BLOCKS-CORRECTNESS-4))
 (6 6 (:TYPE-PRESCRIPTION ZP))
 )
