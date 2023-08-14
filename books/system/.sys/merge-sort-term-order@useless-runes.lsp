(STEPS-TO-NIL
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(ACL2-COUNT-EVENS
 (1507 733 (:REWRITE DEFAULT-+-2))
 (1016 733 (:REWRITE DEFAULT-+-1))
 (520 130 (:DEFINITION INTEGER-ABS))
 (520 65 (:DEFINITION LENGTH))
 (325 65 (:DEFINITION LEN))
 (177 175 (:REWRITE DEFAULT-CAR))
 (168 146 (:REWRITE DEFAULT-<-2))
 (168 146 (:REWRITE DEFAULT-<-1))
 (130 130 (:REWRITE DEFAULT-UNARY-MINUS))
 (65 65 (:TYPE-PRESCRIPTION LEN))
 (65 65 (:REWRITE DEFAULT-REALPART))
 (65 65 (:REWRITE DEFAULT-NUMERATOR))
 (65 65 (:REWRITE DEFAULT-IMAGPART))
 (65 65 (:REWRITE DEFAULT-DENOMINATOR))
 (65 65 (:REWRITE DEFAULT-COERCE-2))
 (65 65 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-CDR-WEAK
 (133 66 (:REWRITE DEFAULT-+-2))
 (91 66 (:REWRITE DEFAULT-+-1))
 (64 16 (:REWRITE COMMUTATIVITY-OF-+))
 (64 16 (:DEFINITION INTEGER-ABS))
 (64 8 (:DEFINITION LENGTH))
 (40 8 (:DEFINITION LEN))
 (25 20 (:REWRITE DEFAULT-<-1))
 (23 20 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE DEFAULT-CAR))
 (3 3 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(ACL2-COUNT-CDR
 (177 5 (:DEFINITION ACL2-COUNT))
 (63 30 (:REWRITE DEFAULT-+-2))
 (42 30 (:REWRITE DEFAULT-+-1))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (24 3 (:DEFINITION LENGTH))
 (15 3 (:DEFINITION LEN))
 (10 10 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-ODDS
 (1740 893 (:REWRITE DEFAULT-+-2))
 (1199 893 (:REWRITE DEFAULT-+-1))
 (470 94 (:DEFINITION LEN))
 (203 196 (:REWRITE DEFAULT-<-2))
 (203 196 (:REWRITE DEFAULT-<-1))
 (188 188 (:REWRITE DEFAULT-UNARY-MINUS))
 (118 118 (:REWRITE DEFAULT-CAR))
 (94 94 (:TYPE-PRESCRIPTION LEN))
 (94 94 (:REWRITE DEFAULT-REALPART))
 (94 94 (:REWRITE DEFAULT-NUMERATOR))
 (94 94 (:REWRITE DEFAULT-IMAGPART))
 (94 94 (:REWRITE DEFAULT-DENOMINATOR))
 (94 94 (:REWRITE DEFAULT-COERCE-2))
 (94 94 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:TYPE-PRESCRIPTION EVENS))
 )
(PSEUDO-TERM-LISTP-MERGE-TERM-ORDER
 (3080 28 (:DEFINITION VAR-FN-COUNT-1))
 (2772 28 (:DEFINITION FN-COUNT-EVG-REC))
 (784 784 (:TYPE-PRESCRIPTION LEN))
 (596 321 (:REWRITE DEFAULT-<-2))
 (596 321 (:REWRITE DEFAULT-<-1))
 (560 112 (:DEFINITION MIN-FIXNUM))
 (552 332 (:REWRITE DEFAULT-+-2))
 (462 398 (:REWRITE DEFAULT-CDR))
 (448 56 (:DEFINITION LENGTH))
 (408 8 (:DEFINITION PSEUDO-TERMP))
 (400 80 (:DEFINITION LEN))
 (370 334 (:REWRITE DEFAULT-CAR))
 (364 140 (:REWRITE UNICITY-OF-0))
 (332 332 (:REWRITE DEFAULT-+-1))
 (276 138 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (224 140 (:DEFINITION FIX))
 (150 150 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (112 56 (:REWRITE DEFAULT-*-2))
 (86 86 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (56 56 (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
 (56 56 (:REWRITE DEFAULT-COERCE-2))
 (56 56 (:REWRITE DEFAULT-COERCE-1))
 (56 56 (:REWRITE DEFAULT-*-1))
 (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (28 28 (:REWRITE DEFAULT-SYMBOL-NAME))
 (28 28 (:REWRITE DEFAULT-REALPART))
 (28 28 (:REWRITE DEFAULT-NUMERATOR))
 (28 28 (:REWRITE DEFAULT-IMAGPART))
 (28 28 (:REWRITE DEFAULT-DENOMINATOR))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (16 8 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(PSEUDO-TERM-LISTP-EVENS
 (153 3 (:DEFINITION PSEUDO-TERMP))
 (90 88 (:REWRITE DEFAULT-CDR))
 (74 72 (:REWRITE DEFAULT-CAR))
 (50 50 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (45 9 (:DEFINITION LEN))
 (31 31 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 21 (:TYPE-PRESCRIPTION LEN))
 (18 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 3 (:DEFINITION SYMBOL-LISTP))
 (6 3 (:DEFINITION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(PSEUDO-TERM-LISTP-MERGE-SORT-TERM-ORDER
 (6672 20 (:DEFINITION MERGE-TERM-ORDER))
 (6140 20 (:DEFINITION TERM-ORDER))
 (6120 20 (:DEFINITION TERM-ORDER1))
 (4400 40 (:DEFINITION VAR-FN-COUNT-1))
 (3960 40 (:DEFINITION FN-COUNT-EVG-REC))
 (1200 1200 (:TYPE-PRESCRIPTION VAR-FN-COUNT-1))
 (1047 1047 (:TYPE-PRESCRIPTION LEN))
 (920 480 (:REWRITE DEFAULT-<-2))
 (920 480 (:REWRITE DEFAULT-<-1))
 (800 160 (:DEFINITION MIN-FIXNUM))
 (726 443 (:REWRITE DEFAULT-+-2))
 (643 497 (:REWRITE DEFAULT-CDR))
 (640 80 (:DEFINITION LENGTH))
 (520 200 (:REWRITE UNICITY-OF-0))
 (480 240 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (480 120 (:DEFINITION MV-NTH))
 (443 443 (:REWRITE DEFAULT-+-1))
 (415 83 (:DEFINITION LEN))
 (372 332 (:REWRITE DEFAULT-CAR))
 (320 200 (:DEFINITION FIX))
 (196 42 (:DEFINITION EVENS))
 (160 80 (:REWRITE DEFAULT-*-2))
 (95 5 (:REWRITE PSEUDO-TERM-LISTP-MERGE-TERM-ORDER))
 (80 80 (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
 (80 80 (:REWRITE DEFAULT-COERCE-2))
 (80 80 (:REWRITE DEFAULT-COERCE-1))
 (80 80 (:REWRITE DEFAULT-*-1))
 (74 74 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (51 1 (:DEFINITION PSEUDO-TERMP))
 (40 40 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (40 40 (:REWRITE DEFAULT-SYMBOL-NAME))
 (40 40 (:REWRITE DEFAULT-REALPART))
 (40 40 (:REWRITE DEFAULT-NUMERATOR))
 (40 40 (:REWRITE DEFAULT-IMAGPART))
 (40 40 (:REWRITE DEFAULT-DENOMINATOR))
 (30 10 (:TYPE-PRESCRIPTION MERGE-TERM-ORDER))
 (20 20 (:TYPE-PRESCRIPTION LEXORDER))
 (20 20 (:REWRITE LEXORDER-TRANSITIVE))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
