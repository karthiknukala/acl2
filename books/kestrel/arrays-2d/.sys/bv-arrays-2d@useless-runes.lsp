(BV-ARRAYP-LIST)
(2D-BV-ARRAYP)
(LEN-OF-NTH-WHEN-BV-ARRAYP-LIST
 (128 8 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (47 47 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (36 36 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (35 11 (:REWRITE DEFAULT-CAR))
 (34 10 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (7 7 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (7 7 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 )
(LEN-OF-NTH-WHEN-2D-BV-ARRAYP
 (12 1 (:DEFINITION NTH))
 (7 1 (:DEFINITION TRUE-LISTP))
 (6 2 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (3 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TRUE-LISTP-OF-NTH-WHEN-BV-ARRAYP-LIST
 (96 6 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (45 3 (:DEFINITION TRUE-LISTP))
 (31 31 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (30 30 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (30 30 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (21 9 (:REWRITE DEFAULT-CAR))
 (20 10 (:REWRITE DEFAULT-CDR))
 (16 11 (:REWRITE DEFAULT-<-2))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 12 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (12 12 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (3 3 (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
 (3 3 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (3 3 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
 (1 1 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (1 1 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 )
(TRUE-LISTP-OF-NTH-WHEN-2D-BV-ARRAYP
 (12 1 (:DEFINITION NTH))
 (7 1 (:DEFINITION TRUE-LISTP))
 (6 2 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(LEN-WHEN-2D-BV-ARRAYP)
(TRUE-LISTP-WHEN-2D-BV-ARRAYP)
(BV-ARRAYP-OF-NTH
 (210 14 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (61 61 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (57 11 (:REWRITE DEFAULT-CAR))
 (55 55 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (55 55 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (53 9 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (22 17 (:REWRITE DEFAULT-<-2))
 (22 14 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (17 17 (:REWRITE DEFAULT-<-1))
 (17 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (15 15 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (15 15 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (15 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (7 6 (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (5 5 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
 (3 3 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (3 3 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(ALL-UNSIGNED-BYTE-P-OF-NTH2
 (54 2 (:DEFINITION NTH))
 (44 8 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (33 1 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (16 2 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE DEFAULT-CAR))
 (11 1 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (8 8 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
 (1 1 (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
 (1 1 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (1 1 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(ALL-UNSIGNED-BYTE-P-OF-NTH3
 (30 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (27 1 (:DEFINITION NTH))
 (18 1 (:DEFINITION TRUE-LISTP))
 (16 2 (:REWRITE DEFAULT-CDR))
 (8 1 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (6 6 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(UNSIGNED-BYTE-P-OF-ARRAY-ELEM-2D
 (39 2 (:DEFINITION NTH))
 (21 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (11 2 (:REWRITE DEFAULT-CDR))
 (11 2 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (6 6 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (6 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(NATP-OF-ARRAY-ELEM-2D
 (10 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 )
(BV-ARRAYP-LIST-OF-CONS
 (92 7 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (78 5 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (31 7 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (12 12 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (7 7 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 5 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (4 4 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (4 4 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(2D-BV-ARRAYP-OF-CONS
 (96 8 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (56 4 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (24 8 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (19 19 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (19 19 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (18 18 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (14 7 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (8 8 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (8 4 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BV-ARRAYP-LIST-OF-APPEND
 (842 58 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (477 30 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (239 56 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (112 85 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (85 85 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (85 85 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (72 36 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (66 35 (:REWRITE DEFAULT-<-2))
 (58 58 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (52 52 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (52 52 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (38 30 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (37 37 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (35 35 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (28 28 (:REWRITE DEFAULT-CDR))
 (6 2 (:DEFINITION NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(BV-ARRAYP-LIST-OF-REVERSE
 (1633 10 (:DEFINITION BINARY-APPEND))
 (1159 59 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (534 5 (:REWRITE NTH-OF-TAKE-GEN2))
 (475 15 (:DEFINITION NTH))
 (449 21 (:REWRITE TAKE-DOES-NOTHING))
 (334 334 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (249 203 (:REWRITE DEFAULT-+-2))
 (247 38 (:REWRITE DEFAULT-CAR))
 (242 227 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (232 14 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (212 212 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (208 6 (:REWRITE CDR-OF-TAKE))
 (203 203 (:REWRITE DEFAULT-+-1))
 (176 34 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (144 5 (:REWRITE TAKE-OF-TAKE-WHEN-<=))
 (142 111 (:REWRITE DEFAULT-<-2))
 (140 15 (:REWRITE LEN-OF-REVERSE-LIST))
 (136 26 (:REWRITE ZP-OPEN))
 (124 11 (:REWRITE CONSP-OF-TAKE))
 (115 111 (:REWRITE DEFAULT-<-1))
 (78 26 (:REWRITE DEFAULT-CDR))
 (68 15 (:REWRITE LEN-OF-TAKE))
 (59 59 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (53 15 (:DEFINITION NFIX))
 (40 40 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (26 6 (:DEFINITION NATP))
 (22 22 (:REWRITE EQUAL-OF-LEN-AND-0))
 (20 20 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (18 14 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (17 5 (:REWRITE BV-ARRAYP-OF-NTH))
 (15 15 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (13 13 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (13 13 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (13 13 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (12 6 (:REWRITE CAR-OF-TAKE-STRONG))
 (11 11 (:TYPE-PRESCRIPTION TAKE))
 (10 10 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (10 10 (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
 (10 10 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (10 10 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS
 (12 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(BV-ARRAYP-OF-COLS-TO-ROW
 (659 48 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (266 12 (:DEFINITION NTH))
 (110 110 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (108 6 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (104 66 (:REWRITE DEFAULT-<-2))
 (81 8 (:REWRITE LEN-OF-COLS-TO-ROW))
 (66 66 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (44 44 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (43 39 (:REWRITE DEFAULT-+-2))
 (39 39 (:REWRITE DEFAULT-+-1))
 (35 29 (:REWRITE DEFAULT-CAR))
 (34 34 (:TYPE-PRESCRIPTION COLS-TO-ROW))
 (33 27 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (16 12 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (12 12 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(BV-ARRAYP-LIST-OF-COLS-TO-ROW-AUX
 (196 14 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (90 5 (:DEFINITION TRUE-LISTP))
 (66 14 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (61 61 (:TYPE-PRESCRIPTION LEN))
 (37 29 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (29 29 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (29 29 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (26 21 (:REWRITE DEFAULT-<-2))
 (24 21 (:REWRITE DEFAULT-<-1))
 (21 21 (:TYPE-PRESCRIPTION COLS-TO-ARRAY-AUX))
 (16 8 (:REWRITE LEN-OF-COLS-TO-ARRAY-AUX))
 (14 14 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(BV-ARRAYP-LIST-OF-COLS-TO-ARRAY
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 1 (:DEFINITION TRUE-LISTP))
 (14 1 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (6 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (4 4 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(2D-BV-ARRAYP-OF-COLS-TO-ARRAY
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 1 (:DEFINITION TRUE-LISTP))
 (14 1 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (6 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(BV-ARRAYP-LIST-OF-REPEAT
 (253 26 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (145 15 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (71 71 (:REWRITE DEFAULT-<-2))
 (71 71 (:REWRITE DEFAULT-<-1))
 (53 53 (:TYPE-PRESCRIPTION LEN))
 (50 10 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (49 13 (:REWRITE LEN-OF-REPEAT))
 (46 33 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (36 12 (:DEFINITION NFIX))
 (33 33 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (26 26 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (21 21 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-+-1))
 (20 20 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (19 15 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (12 12 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(BV-ARRAYP-LIST-OF-TAKE
 (1904 168 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1575 61 (:REWRITE TAKE-DOES-NOTHING))
 (423 423 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (311 311 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (287 66 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (279 191 (:REWRITE DEFAULT-+-2))
 (272 191 (:REWRITE DEFAULT-<-2))
 (202 191 (:REWRITE DEFAULT-<-1))
 (191 191 (:REWRITE DEFAULT-+-1))
 (168 168 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (136 136 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (50 50 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (50 50 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (43 35 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (38 38 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (24 24 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (7 7 (:REWRITE BV-ARRAYP-WHEN-LENGTH-IS-0))
 (6 2 (:DEFINITION NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(BV-ARRAYP-LIST-OF-NTHCDR
 (850 60 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (230 8 (:REWRITE LEN-OF-NTHCDR))
 (190 10 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (181 12 (:REWRITE DEFAULT-CDR))
 (170 4 (:DEFINITION NTH))
 (140 36 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (129 129 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (98 98 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (98 98 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (89 68 (:REWRITE DEFAULT-<-2))
 (78 59 (:REWRITE DEFAULT-+-2))
 (70 68 (:REWRITE DEFAULT-<-1))
 (60 60 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (59 59 (:REWRITE DEFAULT-+-1))
 (57 11 (:REWRITE DEFAULT-CAR))
 (36 4 (:REWRITE COMMUTATIVITY-2-OF-+))
 (31 31 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (30 10 (:REWRITE COMMUTATIVITY-OF-+))
 (28 4 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (15 9 (:REWRITE ZP-OPEN))
 (14 10 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (13 13 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (13 13 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:DEFINITION POSP))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 6 (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
 (9 9 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (6 6 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (6 6 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (6 6 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 (6 6 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BV-ARRAYP-LIST-OF-SUBRANGE
 (44 2 (:REWRITE TAKE-DOES-NOTHING))
 (15 11 (:REWRITE DEFAULT-<-1))
 (12 11 (:REWRITE DEFAULT-<-2))
 (12 10 (:REWRITE DEFAULT-+-2))
 (12 10 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (6 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:DEFINITION POSP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(2D-BV-ARRAYP-OF-SUBRANGE
 (25 2 (:REWRITE TAKE-DOES-NOTHING))
 (15 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (8 1 (:DEFINITION TRUE-LISTP))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (3 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (3 1 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (3 1 (:DEFINITION POSP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(BV-ARRAYP-OF-GET-COLUMN
 (3257 248 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2025 57 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (1489 67 (:DEFINITION NTH))
 (507 507 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (484 311 (:REWRITE DEFAULT-<-2))
 (391 391 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (312 311 (:REWRITE DEFAULT-<-1))
 (250 19 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (248 248 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (223 167 (:REWRITE DEFAULT-CDR))
 (217 217 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (217 7 (:DEFINITION MEMBER-EQUAL))
 (177 156 (:REWRITE DEFAULT-CAR))
 (176 160 (:REWRITE DEFAULT-+-2))
 (160 160 (:REWRITE DEFAULT-+-1))
 (82 82 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (82 82 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (68 60 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (67 67 (:REWRITE ZP-OPEN))
 (67 67 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (60 60 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (38 38 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (35 35 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (23 23 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (15 15 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (15 15 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (8 8 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(2D-BV-ARRAYP-OF-GET-COLUMNS
 (30 5 (:DEFINITION TRUE-LISTP))
 (15 15 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (15 15 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (10 10 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (10 9 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(2D-BV-ARRAYP-OF-GET-COLUMNS-SPECIAL-CASE
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP)
(2D-ARRAY-HEIGHT-WHEN-2D-BV-ARRAYP
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(2D-ARRAY-WIDTH-WHEN-2D-BV-ARRAYP
 (78 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (68 13 (:DEFINITION TRUE-LISTP))
 (49 49 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (49 49 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (49 49 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (30 19 (:REWRITE DEFAULT-<-2))
 (28 20 (:REWRITE DEFAULT-CDR))
 (26 26 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (26 26 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (22 19 (:REWRITE DEFAULT-<-1))
 (22 14 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (21 13 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (19 19 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (14 14 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (14 7 (:DEFINITION NTH))
 (7 7 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (7 7 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (7 7 (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
 (7 7 (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALL-UNSIGNED-BYTE-P-OF-GET-COLUMN
 (1263 90 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (725 19 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (508 23 (:DEFINITION NTH))
 (270 29 (:REWRITE LEN-OF-CDR))
 (179 110 (:REWRITE DEFAULT-<-2))
 (177 177 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (162 148 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (135 14 (:REWRITE LEN-OF-GET-COLUMN))
 (112 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (110 110 (:REWRITE DEFAULT-<-1))
 (99 3 (:DEFINITION MEMBER-EQUAL))
 (90 90 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (83 83 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (77 71 (:REWRITE DEFAULT-CDR))
 (61 61 (:TYPE-PRESCRIPTION GET-COLUMN))
 (60 54 (:REWRITE DEFAULT-CAR))
 (57 53 (:REWRITE DEFAULT-+-2))
 (53 53 (:REWRITE DEFAULT-+-1))
 (28 28 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (28 28 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (24 20 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (23 23 (:REWRITE ZP-OPEN))
 (23 23 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (23 23 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (23 23 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (19 19 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (18 18 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 1 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (3 3 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 )
(BV-ARRAYP-OF-GET-COLUMN-2
 (50 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (40 1 (:DEFINITION GET-COLUMN))
 (22 1 (:DEFINITION NTH))
 (18 1 (:DEFINITION TRUE-LISTP))
 (14 1 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (9 5 (:REWRITE DEFAULT-<-2))
 (8 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NTH-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (1 1 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (1 1 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 )
(TRUE-LIST-LISTP-WHEN-BV-ARRAYP-LIST
 (372 26 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (108 6 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (92 26 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (44 44 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (42 42 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (42 42 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (36 18 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (24 2 (:REWRITE LEN-OF-CDR))
 (18 18 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (17 17 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (14 14 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (6 6 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(ITEMS-HAVE-LEN-WHEN-BV-ARRAYP-LIST
 (589 38 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (180 19 (:REWRITE LEN-OF-CDR))
 (159 9 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (126 30 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (108 108 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (89 89 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (38 38 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (37 23 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (31 31 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (26 26 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (26 22 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-+-1))
 (22 6 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
 (16 16 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (14 14 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (13 13 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 (3 3 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(2D-ARRAYP-WHEN-2D-BV-ARRAYP
 (309 16 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (161 6 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (95 8 (:REWRITE LEN-OF-CDR))
 (72 4 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (67 14 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (43 43 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (35 35 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (32 2 (:REWRITE ITEMS-HAVE-LEN-WHEN-NOT-CONSP))
 (21 10 (:REWRITE DEFAULT-<-2))
 (17 9 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (11 11 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (10 10 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (10 10 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE EQUAL-OF-LEN-AND-0))
 (7 7 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (5 1 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
 (4 4 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(2D-BV-ARRAYP-OF-NTHCDR
 (154 14 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (119 7 (:DEFINITION TRUE-LISTP))
 (98 7 (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
 (52 35 (:REWRITE DEFAULT-<-2))
 (51 35 (:REWRITE DEFAULT-<-1))
 (40 26 (:REWRITE DEFAULT-+-1))
 (38 26 (:REWRITE DEFAULT-+-2))
 (36 36 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
 (35 35 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (35 35 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (14 14 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (14 14 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
 (14 14 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (14 14 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (8 8 (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (3 1 (:DEFINITION POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 )
