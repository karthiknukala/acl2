(COMPUTE-SERIES)
(TYPE-OF-COMPUTE-SERIES (256 256 (:REWRITE DEFAULT-*-2))
                        (256 256 (:REWRITE DEFAULT-*-1))
                        (182 182 (:REWRITE DEFAULT-+-2))
                        (182 182 (:REWRITE DEFAULT-+-1))
                        (104 72 (:REWRITE FOLD-CONSTS-IN-+))
                        (48 8 (:REWRITE ASSOCIATIVITY-OF-+))
                        (40 8 (:REWRITE ASSOCIATIVITY-OF-*))
                        (22 10 (:REWRITE ZP-OPEN))
                        (14 14 (:REWRITE DEFAULT-UNARY-/))
                        (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
                        (4 4 (:REWRITE DEFAULT-<-2))
                        (4 4 (:REWRITE DEFAULT-<-1)))
(FAST-COMPUTE-SERIES)
(TYPE-OF-FAST-COMPUTE-SERIES (540 540 (:REWRITE DEFAULT-*-2))
                             (540 540 (:REWRITE DEFAULT-*-1))
                             (492 492 (:REWRITE DEFAULT-+-2))
                             (492 492 (:REWRITE DEFAULT-+-1))
                             (360 72 (:REWRITE ASSOCIATIVITY-OF-*))
                             (216 72 (:REWRITE FOLD-CONSTS-IN-+))
                             (86 32 (:REWRITE ZP-OPEN))
                             (35 35 (:REWRITE DEFAULT-<-2))
                             (35 35 (:REWRITE DEFAULT-<-1))
                             (34 18 (:REWRITE DEFAULT-CDR))
                             (29 29 (:REWRITE DEFAULT-UNARY-MINUS))
                             (25 13 (:REWRITE DEFAULT-CAR)))
(FAST-COMPUTE-COS)
(FAST-COMPUTE-SIN)
(TRUNCATED-INTEGER-COS (40 1 (:DEFINITION FAST-COMPUTE-SERIES))
                       (16 9 (:REWRITE DEFAULT-*-2))
                       (13 9 (:REWRITE DEFAULT-*-1))
                       (9 3 (:REWRITE UNICITY-OF-1))
                       (6 3 (:DEFINITION FIX))
                       (5 3 (:REWRITE DEFAULT-+-2))
                       (5 3 (:REWRITE DEFAULT-+-1))
                       (5 1 (:REWRITE COMMUTATIVITY-OF-+))
                       (2 2 (:REWRITE DEFAULT-NUMERATOR))
                       (2 2 (:REWRITE DEFAULT-DENOMINATOR))
                       (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                       (1 1 (:REWRITE ZP-OPEN))
                       (1 1 (:REWRITE DEFAULT-<-2))
                       (1 1 (:REWRITE DEFAULT-<-1)))
(TRUNCATED-INTEGER-SIN (31 1 (:DEFINITION FAST-COMPUTE-SERIES))
                       (16 9 (:REWRITE DEFAULT-*-2))
                       (13 9 (:REWRITE DEFAULT-*-1))
                       (5 3 (:REWRITE DEFAULT-+-2))
                       (5 3 (:REWRITE DEFAULT-+-1))
                       (5 1 (:REWRITE COMMUTATIVITY-OF-+))
                       (4 4 (:REWRITE DEFAULT-NUMERATOR))
                       (3 3 (:REWRITE DEFAULT-DENOMINATOR))
                       (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                       (1 1 (:REWRITE ZP-OPEN))
                       (1 1 (:REWRITE DEFAULT-<-2))
                       (1 1 (:REWRITE DEFAULT-<-1)))
(TRUNCATED-INTEGER-SIN/COS-TABLE-FN
     (76 76 (:REWRITE DEFAULT-*-2))
     (76 76 (:REWRITE DEFAULT-*-1))
     (70 70 (:REWRITE DEFAULT-UNARY-/))
     (32 28 (:REWRITE DEFAULT-<-1))
     (31 28 (:REWRITE DEFAULT-<-2))
     (28 22 (:REWRITE DEFAULT-+-2))
     (26 22 (:REWRITE DEFAULT-+-1))
     (21 21
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(TRUNCATED-INTEGER-SIN/COS-TABLE)