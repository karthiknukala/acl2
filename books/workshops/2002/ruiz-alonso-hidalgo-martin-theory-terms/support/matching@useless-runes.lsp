(A-PAIR)
(A-PAIR-SELECTED (2 2 (:REWRITE DEFAULT-CAR)))
(TRANSFORM-SUBS-SEL (12 6
                        (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
                    (6 6 (:TYPE-PRESCRIPTION ALISTP)))
(MEMBER-MATCHER (72 12 (:DEFINITION VAL)))
(SUBSETP-MATCHER (108 108 (:REWRITE DEFAULT-CAR))
                 (99 11 (:DEFINITION APPLY-SUBST))
                 (75 75 (:REWRITE DEFAULT-CDR))
                 (66 11 (:DEFINITION VAL))
                 (60 13 (:DEFINITION MEMBER-EQUAL))
                 (8 8 (:REWRITE SUBSETP-TRANSITIVE)))
(EQUAL-SET-IMPLIES-IFF-MATCHER-2 (34 2 (:DEFINITION MATCHER))
                                 (32 4 (:DEFINITION SUBSETP-EQUAL))
                                 (22 22 (:REWRITE DEFAULT-CAR))
                                 (18 18 (:REWRITE DEFAULT-CDR))
                                 (18 2 (:DEFINITION APPLY-SUBST))
                                 (12 4 (:DEFINITION MEMBER-EQUAL))
                                 (12 2 (:DEFINITION VAL))
                                 (8 8 (:REWRITE SUBSETP-TRANSITIVE))
                                 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                                 (2 2 (:REWRITE MEMBER-MATCHER)))
(EQUAL-SET-SELECTION-AND-ELIMINATE-LEMMA (632 595 (:REWRITE DEFAULT-CAR))
                                         (574 545 (:REWRITE DEFAULT-CDR)))
(EQUAL-SET-SELECTION-AND-ELIMINATE (7 7 (:REWRITE DEFAULT-CAR))
                                   (5 1 (:DEFINITION ELIMINATE))
                                   (2 2 (:REWRITE SUBSETP-TRANSITIVE))
                                   (2 2 (:REWRITE DEFAULT-CDR)))
(MATCHER-APPEND (231 213 (:REWRITE DEFAULT-CAR))
                (174 29 (:DEFINITION VAL))
                (151 145 (:REWRITE DEFAULT-CDR))
                (50 25
                    (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (25 25 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(INDUCTION-PAIR-ARGS (121 58 (:REWRITE DEFAULT-+-2))
                     (81 58 (:REWRITE DEFAULT-+-1))
                     (48 12 (:REWRITE COMMUTATIVITY-OF-+))
                     (48 12 (:DEFINITION INTEGER-ABS))
                     (48 6 (:DEFINITION LENGTH))
                     (30 6 (:DEFINITION LEN))
                     (21 16 (:REWRITE DEFAULT-<-2))
                     (20 16 (:REWRITE DEFAULT-<-1))
                     (19 19 (:REWRITE DEFAULT-CDR))
                     (17 17 (:REWRITE FOLD-CONSTS-IN-+))
                     (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
                     (10 10 (:REWRITE DEFAULT-CAR))
                     (6 6 (:TYPE-PRESCRIPTION LEN))
                     (6 6 (:REWRITE DEFAULT-REALPART))
                     (6 6 (:REWRITE DEFAULT-NUMERATOR))
                     (6 6 (:REWRITE DEFAULT-IMAGPART))
                     (6 6 (:REWRITE DEFAULT-DENOMINATOR))
                     (6 6 (:REWRITE DEFAULT-COERCE-2))
                     (6 6 (:REWRITE DEFAULT-COERCE-1)))
(MATCHER-PAIR-ARGS (415 268 (:REWRITE DEFAULT-CAR))
                   (291 241 (:REWRITE DEFAULT-CDR))
                   (108 18 (:DEFINITION VAL))
                   (24 6
                       (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE)))
(MATCHER-SIGMA-VALUE (371 187
                          (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
                     (122 122 (:REWRITE DEFAULT-CAR))
                     (58 58 (:REWRITE DEFAULT-CDR)))
(PAIR-ARGS-APPLY-SUBST (47 24 (:REWRITE DEFAULT-CAR))
                       (28 19 (:REWRITE DEFAULT-CDR))
                       (7 1 (:DEFINITION VAL))
                       (6 6
                          (:REWRITE APPLY-CONSP-IS-CONSP-LIST-OF-TERMS))
                       (2 2 (:REWRITE MATCHER-SIGMA-VALUE)))
(MATCHER-TOPMOST-FUNCTION-SYMBOL (12 12 (:REWRITE DEFAULT-CAR))
                                 (5 5 (:REWRITE DEFAULT-CDR)))
(MATCHER-VARIABLE-NON-VARIABLE (3 1 (:DEFINITION APPLY-SUBST))
                               (1 1 (:REWRITE DEFAULT-CDR))
                               (1 1 (:REWRITE DEFAULT-CAR)))
(MATCHER-NOT-PAIR-ARGS (120 63 (:REWRITE DEFAULT-CAR))
                       (80 62 (:REWRITE DEFAULT-CDR))
                       (7 1 (:DEFINITION VAL))
                       (6 6
                          (:REWRITE APPLY-CONSP-IS-CONSP-LIST-OF-TERMS))
                       (2 2 (:REWRITE MATCHER-SIGMA-VALUE))
                       (1 1
                          (:REWRITE MATCHER-VARIABLE-NON-VARIABLE))
                       (1 1
                          (:REWRITE MATCHER-TOPMOST-FUNCTION-SYMBOL)))
(MATCHER-ASSOC (39 21
                   (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
               (15 15 (:REWRITE DEFAULT-CAR))
               (15 3 (:DEFINITION ASSOC-EQUAL))
               (14 2 (:DEFINITION VAL))
               (7 7 (:REWRITE DEFAULT-CDR)))
(TRANSFORM-SUBS-SEL-PRESERVES-MATCHERS-1
     (6639 63 (:REWRITE MATCHER-ASSOC))
     (5313 345 (:DEFINITION ASSOC-EQUAL))
     (1033 328
           (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (412 328 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (328 328 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (205 41 (:DEFINITION ELIMINATE))
     (62 22
         (:REWRITE MATCHER-VARIABLE-NON-VARIABLE))
     (38 8 (:DEFINITION BINARY-APPEND)))
(TRANSFORM-SUBS-SEL-PRESERVES-MATCHERS-2
     (8295 89 (:REWRITE MATCHER-ASSOC))
     (1114 425
           (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (467 425 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (425 425 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (165 33 (:DEFINITION ELIMINATE))
     (93 31
         (:REWRITE MATCHER-VARIABLE-NON-VARIABLE))
     (93 31
         (:REWRITE MATCHER-TOPMOST-FUNCTION-SYMBOL))
     (93 31 (:REWRITE MATCHER-NOT-PAIR-ARGS))
     (72 4 (:DEFINITION PAIR-ARGS))
     (63 15 (:DEFINITION BINARY-APPEND)))
(TRANSFORM-SUBS-SEL-FAIL (1089 24 (:REWRITE MATCHER-ASSOC))
                         (882 66 (:DEFINITION ASSOC-EQUAL))
                         (694 304
                              (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
                         (389 346 (:REWRITE DEFAULT-CAR))
                         (200 185 (:REWRITE DEFAULT-CDR))
                         (91 13 (:DEFINITION VAL))
                         (70 35
                             (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                         (65 13 (:DEFINITION ELIMINATE))
                         (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
                         (35 35 (:TYPE-PRESCRIPTION BINARY-APPEND))
                         (27 9
                             (:REWRITE MATCHER-VARIABLE-NON-VARIABLE))
                         (17 5 (:DEFINITION BINARY-APPEND))
                         (8 8 (:REWRITE CDR-CONS)))
(NOT-ASSOC-NOT-MEMBER-DOMAIN
     (313 158
          (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
     (137 106 (:REWRITE DEFAULT-CAR))
     (132 11 (:REWRITE ASSOC-MEMBER-DOMAIN))
     (99 11 (:DEFINITION ALISTP))
     (63 32 (:REWRITE DEFAULT-CDR))
     (54 36
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
     (30 30 (:REWRITE CONSP-DOMAIN)))
(TRANSFORM-SUBS-SEL-PRESERVES-SYSTEM-SUBSTITUTION
     (81 52 (:REWRITE DEFAULT-CDR))
     (52 4 (:DEFINITION MEMBER-EQUAL))
     (48 4 (:REWRITE ASSOC-MEMBER-DOMAIN))
     (36 4 (:DEFINITION ALISTP))
     (28 28 (:TYPE-PRESCRIPTION DOMAIN))
     (24 6 (:DEFINITION DOMAIN))
     (18 1 (:DEFINITION PAIR-ARGS))
     (15 3 (:DEFINITION ASSOC-EQUAL))
     (12 12 (:REWRITE CONSP-DOMAIN))
     (6 1 (:DEFINITION VAL))
     (5 1 (:DEFINITION BINARY-APPEND))
     (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL)))
(MATCHER-EXTENDED (380 340 (:REWRITE DEFAULT-CAR))
                  (192 16 (:REWRITE ASSOC-MEMBER-DOMAIN))
                  (188 148 (:REWRITE DEFAULT-CDR))
                  (144 16 (:DEFINITION ALISTP))
                  (80 80 (:TYPE-PRESCRIPTION ALISTP))
                  (66 44
                      (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
                  (36 36 (:REWRITE CONSP-DOMAIN)))
(SYSTEM-SUBSTITUTIONS-MAIN-PROPERTY
     (318 276 (:REWRITE DEFAULT-CAR))
     (187 145 (:REWRITE DEFAULT-CDR))
     (182 14 (:DEFINITION MEMBER-EQUAL))
     (168 14 (:REWRITE ASSOC-MEMBER-DOMAIN))
     (126 14 (:DEFINITION ALISTP))
     (98 98 (:TYPE-PRESCRIPTION DOMAIN))
     (81 54
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
     (70 70 (:TYPE-PRESCRIPTION ALISTP))
     (56 14 (:DEFINITION DOMAIN))
     (42 42 (:REWRITE CONSP-DOMAIN)))
(LENGTH-SYSTEM-POSITIVE-IF-CONSP (53 25 (:REWRITE DEFAULT-+-2))
                                 (45 9 (:DEFINITION LENGTH-TERM))
                                 (39 25 (:REWRITE DEFAULT-+-1))
                                 (16 16 (:REWRITE DEFAULT-CDR))
                                 (12 12 (:REWRITE DEFAULT-CAR))
                                 (8 8 (:REWRITE FOLD-CONSTS-IN-+)))
(LENGTH-SYSTEM-APPEND (203 93 (:REWRITE DEFAULT-+-2))
                      (157 93 (:REWRITE DEFAULT-+-1))
                      (150 30 (:DEFINITION LENGTH-TERM))
                      (95 14
                          (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
                      (78 39
                          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                      (63 60 (:REWRITE DEFAULT-CDR))
                      (54 48 (:REWRITE DEFAULT-CAR))
                      (39 39 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (39 39 (:TYPE-PRESCRIPTION BINARY-APPEND))
                      (29 29 (:REWRITE FOLD-CONSTS-IN-+)))
(ELIMINATE-NOT-MEMBER (164 76 (:REWRITE DEFAULT-+-2))
                      (140 28 (:DEFINITION LENGTH-TERM))
                      (124 76 (:REWRITE DEFAULT-+-1))
                      (59 58 (:REWRITE DEFAULT-CDR))
                      (59 57 (:REWRITE DEFAULT-CAR))
                      (24 24 (:REWRITE FOLD-CONSTS-IN-+)))
(LENGTH-SYSTEM-ELIMINATE (161 75 (:REWRITE DEFAULT-+-2))
                         (135 27 (:DEFINITION LENGTH-TERM))
                         (119 75 (:REWRITE DEFAULT-+-1))
                         (75 73 (:REWRITE DEFAULT-CAR))
                         (72 71 (:REWRITE DEFAULT-CDR))
                         (38 11
                             (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
                         (24 24 (:REWRITE FOLD-CONSTS-IN-+))
                         (19 9 (:LINEAR ELIMINATE-NOT-MEMBER))
                         (18 7 (:REWRITE DEFAULT-<-2))
                         (16 7 (:REWRITE DEFAULT-<-1)))
(LENGTH-SYSTEM-ELIMINATE-LEQ (176 81 (:REWRITE DEFAULT-+-2))
                             (145 29 (:DEFINITION LENGTH-TERM))
                             (133 81 (:REWRITE DEFAULT-+-1))
                             (90 89 (:REWRITE DEFAULT-CDR))
                             (84 82 (:REWRITE DEFAULT-CAR))
                             (63 7 (:REWRITE ELIMINATE-NOT-MEMBER))
                             (26 26 (:REWRITE FOLD-CONSTS-IN-+))
                             (26 8
                                 (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
                             (16 6 (:REWRITE DEFAULT-<-1))
                             (14 6 (:REWRITE DEFAULT-<-2)))
(LENGTH-SYSTEM-SELECTION-AND-DELETE-ONE-LEMMA
     (652 294 (:REWRITE DEFAULT-+-2))
     (462 294 (:REWRITE DEFAULT-+-1)))
(LENGTH-SYSTEM-SELECTION-AND-DELETE-ONE
     (154 70 (:REWRITE DEFAULT-+-2))
     (140 28 (:DEFINITION LENGTH-TERM))
     (112 70 (:REWRITE DEFAULT-+-1))
     (77 76 (:REWRITE DEFAULT-CAR))
     (77 7 (:REWRITE COMMUTATIVITY-2-OF-+))
     (65 65 (:REWRITE DEFAULT-CDR))
     (35 7 (:REWRITE COMMUTATIVITY-OF-+))
     (25 5 (:DEFINITION DELETE-ONE))
     (21 21 (:REWRITE FOLD-CONSTS-IN-+))
     (5 1 (:DEFINITION ELIMINATE)))
(LENGTH-SYSTEM-ELIMINATE-DELETE-ONE-X
     (486 223 (:REWRITE DEFAULT-+-2))
     (405 81 (:DEFINITION LENGTH-TERM))
     (365 223 (:REWRITE DEFAULT-+-1))
     (223 221 (:REWRITE DEFAULT-CDR))
     (196 192 (:REWRITE DEFAULT-CAR))
     (126 14 (:REWRITE ELIMINATE-NOT-MEMBER))
     (71 71 (:REWRITE FOLD-CONSTS-IN-+))
     (39 18
         (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
     (14 6 (:REWRITE DEFAULT-<-2))
     (14 6 (:REWRITE DEFAULT-<-1)))
(LENGTH-SIZE-PAIR-ARGS
     (360 168 (:REWRITE DEFAULT-+-2))
     (337 196 (:REWRITE DEFAULT-CAR))
     (294 168 (:REWRITE DEFAULT-+-1))
     (212 177 (:REWRITE DEFAULT-CDR))
     (104 13
          (:REWRITE LENGTH-SYSTEM-SELECTION-AND-DELETE-ONE))
     (84 21
         (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
     (42 42 (:REWRITE FOLD-CONSTS-IN-+))
     (26 13
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE)))
(TRANSFORM-SUBS-SEL-DECREASES-LENGTH-OF-FIRST-SYSTEM
     (710 318 (:REWRITE DEFAULT-+-2))
     (512 318 (:REWRITE DEFAULT-+-1))
     (130 26 (:DEFINITION DELETE-ONE))
     (85 17 (:DEFINITION ELIMINATE))
     (84 42
         (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
     (72 4 (:DEFINITION PAIR-ARGS))
     (48 16 (:REWRITE ELIMINATE-NOT-MEMBER))
     (44 44 (:TYPE-PRESCRIPTION ELIMINATE))
     (21 6
         (:LINEAR LENGTH-SYSTEM-POSITIVE-IF-CONSP))
     (15 7
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
     (12 4 (:LINEAR ELIMINATE-NOT-MEMBER))
     (12 3 (:REWRITE DEFAULT-<-2))
     (10 3 (:REWRITE DEFAULT-<-1))
     (6 1 (:DEFINITION VAL))
     (5 1 (:DEFINITION BINARY-APPEND))
     (5 1 (:DEFINITION ASSOC-EQUAL)))
(SYSTEM-S-P-VARIABLE-S-P (60 12 (:DEFINITION LEN))
                         (58 58 (:REWRITE DEFAULT-CAR))
                         (50 50 (:REWRITE DEFAULT-CDR))
                         (24 12 (:REWRITE DEFAULT-+-2))
                         (21 14
                             (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
                         (12 12 (:TYPE-PRESCRIPTION LEN))
                         (12 12
                             (:REWRITE SYSTEM-S-P-TERM-P-AUX-ARGUMENTS))
                         (12 12 (:REWRITE DEFAULT-+-1)))
(TERMP-S-P-MEMBER-SYSTEM-S-P
     (105 21 (:DEFINITION LEN))
     (71 71 (:REWRITE DEFAULT-CAR))
     (42 21 (:REWRITE DEFAULT-+-2))
     (28 19
         (:REWRITE SYSTEM-S-P-TERM-P-AUX-ARGUMENTS))
     (24 16
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
     (21 21 (:TYPE-PRESCRIPTION LEN))
     (21 21 (:REWRITE DEFAULT-+-1))
     (8 8 (:REWRITE SYSTEM-S-P-VARIABLE-S-P))
     (6 6 (:TYPE-PRESCRIPTION VARIABLE-P)))
(TRANSFORM-SUBS-SEL-PRESERVES-SYSTEM-S-P
     (144 3 (:DEFINITION SYSTEM-S-P))
     (115 80 (:REWRITE DEFAULT-CAR))
     (87 6 (:DEFINITION TERM-S-P-AUX))
     (65 60 (:REWRITE DEFAULT-CDR))
     (54 3 (:DEFINITION PAIR-ARGS))
     (30 6 (:DEFINITION LEN))
     (24 12
         (:TYPE-PRESCRIPTION ASSOC-CONSP-OR-NIL))
     (24 4 (:DEFINITION MEMBER-EQUAL))
     (15 10
         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
     (12 12 (:TYPE-PRESCRIPTION ALISTP))
     (12 6 (:REWRITE DEFAULT-+-2))
     (11 3
         (:REWRITE TERMP-S-P-MEMBER-SYSTEM-S-P))
     (11 3 (:REWRITE SYSTEM-S-P-VARIABLE-S-P))
     (10 2 (:DEFINITION ELIMINATE))
     (10 2 (:DEFINITION BINARY-APPEND))
     (6 6 (:TYPE-PRESCRIPTION LEN))
     (6 6 (:REWRITE DEFAULT-+-1))
     (6 1 (:DEFINITION VAL))
     (5 1 (:DEFINITION ASSOC-EQUAL)))
(TRANSFORM-SUBS-SEL-SEL-PRESERVES-SUBSTITUTION-S-P
     (135 10 (:DEFINITION TERM-S-P-AUX))
     (102 85 (:REWRITE DEFAULT-CDR))
     (102 3 (:DEFINITION SYSTEM-S-P))
     (72 12 (:DEFINITION MEMBER-EQUAL))
     (50 10 (:DEFINITION LEN))
     (42 10
         (:REWRITE SYSTEM-S-P-TERM-P-AUX-ARGUMENTS))
     (20 10 (:REWRITE DEFAULT-+-2))
     (18 1 (:DEFINITION PAIR-ARGS))
     (15 3 (:DEFINITION ASSOC-EQUAL))
     (10 10 (:TYPE-PRESCRIPTION TERM-S-P-AUX))
     (10 10 (:TYPE-PRESCRIPTION LEN))
     (10 10 (:REWRITE DEFAULT-+-1))
     (6 1 (:DEFINITION VAL))
     (5 1 (:DEFINITION BINARY-APPEND)))
(SUBS-SYSTEM-SEL (113 3 (:DEFINITION LENGTH-SYSTEM))
                 (39 18 (:REWRITE DEFAULT-+-2))
                 (33 3 (:REWRITE COMMUTATIVITY-2-OF-+))
                 (30 18 (:REWRITE DEFAULT-+-1))
                 (30 6 (:DEFINITION LENGTH-TERM))
                 (24 24 (:TYPE-PRESCRIPTION LENGTH-TERM))
                 (22 19 (:REWRITE DEFAULT-CAR))
                 (15 3 (:REWRITE COMMUTATIVITY-OF-+))
                 (14 14 (:REWRITE DEFAULT-CDR))
                 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                 (5 1 (:DEFINITION ELIMINATE))
                 (1 1 (:TYPE-PRESCRIPTION SUBS-SYSTEM-SEL)))
(IF-MATCHABLE-TRANSFORM-SUBS-SEL-SUCCESS)
(SUBS-SYSTEM-SEL-PRESERVES-MATCHERS-1
     (140 140 (:REWRITE DEFAULT-CAR))
     (104 12
          (:REWRITE TRANSFORM-SUBS-SEL-PRESERVES-MATCHERS-2))
     (104 12 (:REWRITE TRANSFORM-SUBS-SEL-FAIL))
     (99 11 (:DEFINITION APPLY-SUBST))
     (66 11 (:DEFINITION VAL))
     (63 63 (:REWRITE DEFAULT-CDR))
     (40 26 (:TYPE-PRESCRIPTION SUBS-SYSTEM-SEL))
     (24 24
         (:TYPE-PRESCRIPTION TRANSFORM-SUBS-SEL))
     (20 4 (:DEFINITION ELIMINATE))
     (6 2
        (:REWRITE IF-MATCHABLE-TRANSFORM-SUBS-SEL-SUCCESS)))
(SUBS-SYSTEM-SEL-PRESERVES-MATCHERS-2
     (179 179 (:REWRITE DEFAULT-CAR))
     (99 11 (:DEFINITION APPLY-SUBST))
     (83 10 (:REWRITE TRANSFORM-SUBS-SEL-FAIL))
     (75 75 (:REWRITE DEFAULT-CDR))
     (66 11 (:DEFINITION VAL))
     (50 10 (:DEFINITION ELIMINATE))
     (39 3
         (:REWRITE TRANSFORM-SUBS-SEL-PRESERVES-MATCHERS-1)))
(SUBS-SYSTEM-SEL-FAIL (64 64 (:REWRITE DEFAULT-CAR))
                      (30 2 (:DEFINITION MATCHER))
                      (25 5 (:DEFINITION ELIMINATE))
                      (24 3
                          (:REWRITE TRANSFORM-SUBS-SEL-PRESERVES-MATCHERS-2))
                      (22 4
                          (:REWRITE SUBS-SYSTEM-SEL-PRESERVES-MATCHERS-2))
                      (20 20 (:REWRITE DEFAULT-CDR))
                      (18 2 (:DEFINITION APPLY-SUBST))
                      (12 2 (:DEFINITION VAL)))
(SUBS-SYSTEM-SEL-PRESERVES-SYSTEM-SUBSTITUTION
     (205 166 (:REWRITE DEFAULT-CAR))
     (169 13 (:DEFINITION MEMBER-EQUAL))
     (156 13 (:REWRITE ASSOC-MEMBER-DOMAIN))
     (117 13 (:DEFINITION ALISTP))
     (91 91 (:TYPE-PRESCRIPTION DOMAIN))
     (65 65 (:TYPE-PRESCRIPTION ALISTP))
     (52 13 (:DEFINITION DOMAIN))
     (39 39 (:REWRITE CONSP-DOMAIN))
     (10 2 (:DEFINITION ELIMINATE))
     (4 4 (:REWRITE CAR-CONS)))
(SUBS-SYSTEM-SEL-SUBSTITUTION-S-P
     (320 22 (:DEFINITION TERM-S-P-AUX))
     (110 22 (:DEFINITION LEN))
     (106 22
          (:REWRITE SYSTEM-S-P-TERM-P-AUX-ARGUMENTS))
     (66 9 (:DEFINITION MEMBER-EQUAL))
     (45 45 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (44 22 (:REWRITE DEFAULT-+-2))
     (35 7 (:DEFINITION ELIMINATE))
     (22 22 (:TYPE-PRESCRIPTION LEN))
     (22 22 (:REWRITE DEFAULT-+-1))
     (4 4 (:TYPE-PRESCRIPTION EQLABLEP)))
(MATCH-SEL)
(IN-NORMAL-FORMS-S-IS-MATCHABLE-BY-ANY-SIGMA (36 4 (:DEFINITION APPLY-SUBST))
                                             (24 4 (:DEFINITION VAL))
                                             (22 22 (:REWRITE DEFAULT-CDR))
                                             (5 1 (:DEFINITION ELIMINATE)))
(MATCH-SEL-SOUNDNESS (42 42 (:REWRITE DEFAULT-CAR))
                     (28 28 (:REWRITE DEFAULT-CDR))
                     (28 14
                         (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
                     (27 3 (:DEFINITION APPLY-SUBST))
                     (22 2 (:DEFINITION BINARY-APPEND))
                     (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (20 4 (:DEFINITION TRUE-LISTP))
                     (18 3 (:DEFINITION VAL))
                     (16 2 (:REWRITE APPEND-TO-NIL))
                     (16 2 (:REWRITE APPEND-NIL)))
(MATCH-SEL-COMPLETENESS (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
                        (20 4 (:DEFINITION TRUE-LISTP))
                        (19 1 (:DEFINITION BINARY-APPEND))
                        (16 2 (:REWRITE APPEND-TO-NIL))
                        (16 2 (:REWRITE APPEND-NIL))
                        (11 11 (:REWRITE DEFAULT-CDR))
                        (11 11 (:REWRITE DEFAULT-CAR))
                        (9 1 (:DEFINITION APPLY-SUBST))
                        (8 1 (:DEFINITION SUBS-SYSTEM-SEL))
                        (7 1 (:DEFINITION NORMAL-FORM-SYST))
                        (6 1 (:DEFINITION VAL))
                        (4 2
                           (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE)))
(MATCH-SEL-SUBSTITUTION-S-P (170 11 (:DEFINITION TERM-S-P-AUX))
                            (65 62 (:REWRITE DEFAULT-CAR))
                            (58 55 (:REWRITE DEFAULT-CDR))
                            (55 11
                                (:REWRITE SYSTEM-S-P-TERM-P-AUX-ARGUMENTS))
                            (55 11 (:DEFINITION LEN))
                            (34 20
                                (:REWRITE EQUAL-SET-SELECTION-AND-ELIMINATE))
                            (32 4 (:DEFINITION SUBS-SYSTEM-SEL))
                            (31 1 (:DEFINITION SUBSTITUTION-S-P))
                            (28 4 (:DEFINITION NORMAL-FORM-SYST))
                            (22 11 (:REWRITE DEFAULT-+-2))
                            (18 7 (:DEFINITION MEMBER-EQUAL))
                            (12 12 (:TYPE-PRESCRIPTION VARIABLE-P))
                            (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                            (11 11 (:TYPE-PRESCRIPTION LEN))
                            (11 11 (:REWRITE DEFAULT-+-1))
                            (4 4 (:TYPE-PRESCRIPTION EQLABLEP)))
(SUBS-SEL)
(MATCHING-SEL)
(SUBS-SEL-SOUNDNESS (9 1 (:DEFINITION APPLY-SUBST))
                    (8 8 (:REWRITE DEFAULT-CAR))
                    (6 1 (:DEFINITION VAL))
                    (4 4 (:REWRITE DEFAULT-CDR)))
(SUBS-SEL-COMPLETENESS (27 3 (:DEFINITION APPLY-SUBST))
                       (18 3 (:DEFINITION VAL))
                       (15 15 (:REWRITE DEFAULT-CAR))
                       (11 11 (:REWRITE DEFAULT-CDR)))
(MATCHING-SEL-SUBSTITUTION-S-P (21 18 (:REWRITE DEFAULT-CAR))
                               (20 20 (:REWRITE DEFAULT-CDR))
                               (20 4 (:DEFINITION LEN))
                               (8 4 (:REWRITE DEFAULT-+-2))
                               (4 4 (:TYPE-PRESCRIPTION LEN))
                               (4 4 (:REWRITE DEFAULT-+-1))
                               (3 3 (:TYPE-PRESCRIPTION MATCH-SEL)))