(MOD-EQUAL-IMPOSSIBLE-VALUE
 (117 5 (:REWRITE MOD-IS-0-WHEN-MULTIPLE))
 (45 10 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (37 4 (:REWRITE MOD-WHEN-MULTIPLE))
 (25 10 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (22 19 (:REWRITE DEFAULT-<-1))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE BOUND-WHEN-USB2))
 (19 19 (:REWRITE <-WHEN-BVLT))
 (19 19 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (19 10 (:REWRITE INTEGERP-OF-*))
 (19 10 (:REWRITE DEFAULT-UNARY-/))
 (19 4 (:REWRITE MOD-WHEN-<))
 (17 17 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (17 17 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (17 17 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (15 9 (:REWRITE NOT-<-WHEN-SBVLT))
 (11 9 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (10 10 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (10 10 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (9 9 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (9 9 (:REWRITE BOUND-WHEN-USB))
 (9 9 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (7 7 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (7 7 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (7 7 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (6 6 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (5 5 (:REWRITE MOD-WHEN-<-OF-0))
 (5 5 (:REWRITE DIVISIBLE-WHEN-DIVISIBLE-BY-MULTIPLE))
 (4 4 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (4 4 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (4 4 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (4 4 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (4 4 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (4 4 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (4 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (4 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(FLOOR-OF-SUM-OF-MINUS-EXPT-AND-BVCHOP
 (3916 10 (:REWRITE FLOOR-MUST-BE-1))
 (3624 24 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (3365 52 (:LINEAR BVCHOP-UPPER-BOUND))
 (2926 10 (:REWRITE FLOOR-WHEN-<))
 (2578 22 (:REWRITE SMALL-INT-HACK))
 (2524 10 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
 (2490 10 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (2404 2 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
 (2291 12 (:REWRITE INTEGERP-OF--))
 (2049 2049 (:TYPE-PRESCRIPTION EVENP))
 (1711 603 (:REWRITE DEFAULT-<-2))
 (1617 603 (:REWRITE DEFAULT-<-1))
 (1380 10 (:REWRITE FLOOR-WHEN-<=))
 (1366 683 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (1366 683 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (1366 683 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (1072 2 (:REWRITE <-OF-*-OF-/-ARG2-ALT))
 (920 120 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (920 120 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (860 52 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (794 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (760 60 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (760 60 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (750 64 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (688 43 (:DEFINITION NATP))
 (683 683 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (683 683 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (683 683 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (682 52 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (604 604 (:REWRITE BOUND-WHEN-USB2))
 (604 604 (:REWRITE <-WHEN-BVLT))
 (604 604 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (524 52 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (515 64 (:REWRITE BVCHOP-IDENTITY))
 (491 491 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (491 491 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (491 491 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (482 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (460 60 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (460 60 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (440 52 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (407 254 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (394 82 (:REWRITE DEFAULT-*-2))
 (349 349 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (342 254 (:REWRITE NOT-<-WHEN-SBVLT))
 (333 105 (:REWRITE DEFAULT-+-1))
 (325 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
 (320 34 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (317 34 (:REWRITE DEFAULT-UNARY-MINUS))
 (303 82 (:REWRITE DEFAULT-*-1))
 (300 24 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (254 254 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (254 254 (:REWRITE BOUND-WHEN-USB))
 (254 254 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (232 10 (:REWRITE *-OF---ARG1))
 (230 230 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (227 227 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (227 227 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (227 227 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (211 64 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (211 64 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (210 60 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (206 10 (:REWRITE FLOOR-WHEN-DIVISIBLE-CHEAP))
 (196 196 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (196 196 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (196 196 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (196 196 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (196 196 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (181 181 (:TYPE-PRESCRIPTION NATP))
 (168 84 (:REWRITE GETBIT-WHEN-NOT-0))
 (164 105 (:REWRITE DEFAULT-+-2))
 (146 2 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
 (140 10 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (140 10 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (140 10 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (140 10 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (128 64 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (128 64 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (128 64 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (120 120 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (120 120 (:LINEAR EXPT-BOUND-LINEAR))
 (120 120 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (104 104 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (95 3 (:REWRITE BVCHOP-BOUND-2))
 (85 85 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (84 84 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (84 84 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (84 84 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (84 84 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (84 42 (:REWRITE GETBIT-WHEN-NOT-1))
 (84 34 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (65 65 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (64 64 (:TYPE-PRESCRIPTION POSP))
 (64 64 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (64 64 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (64 64 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (64 64 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (64 64 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (64 64 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (64 64 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (64 64 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (60 60 (:LINEAR EXPT-BOUND-LINEAR-2))
 (54 27 (:REWRITE DEFAULT-UNARY-/))
 (51 24 (:REWRITE INTEGERP-OF-*))
 (49 49 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (49 49 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (49 49 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (49 49 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (49 49 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (49 49 (:REWRITE UBP-LONGER-BETTER))
 (49 49 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (46 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (43 43 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (43 43 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (36 2 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
 (34 34 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (34 34 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (26 2 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
 (24 24 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (23 23 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (23 23 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (15 15 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (15 15 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (15 15 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (12 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (10 10 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (10 10 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (10 10 (:REWRITE FLOOR-DIVIDE-BY-COMMON-CONSTANT-FACTOR))
 (10 10 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (10 10 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (10 10 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (6 6 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (6 6 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (6 6 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (6 6 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE FLOOR-MINUS-ARG1-HACK))
 (6 6 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (6 6 (:REWRITE EQUAL-WHEN-BVLT))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (6 6 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (4 4 (:REWRITE *-OF-0))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-LINEAR))
 (4 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (3 3 (:REWRITE BVCHOP-BOUND))
 (3 3 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (1 1 (:REWRITE BVCHOP-UPPER-BOUND))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 )
(FLOOR-OF-SUM-OF-MINUS-EXPT-AND-BVCHOP-ARG2
 (1037 3 (:REWRITE FLOOR-MUST-BE-1))
 (1004 16 (:LINEAR BVCHOP-UPPER-BOUND))
 (873 3 (:REWRITE FLOOR-WHEN-<))
 (819 1 (:REWRITE DEFAULT-UNARY-/))
 (693 693 (:TYPE-PRESCRIPTION EVENP))
 (462 231 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (462 231 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (462 231 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (426 142 (:REWRITE DEFAULT-<-2))
 (420 3 (:REWRITE FLOOR-WHEN-<=))
 (365 142 (:REWRITE DEFAULT-<-1))
 (337 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (293 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (292 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (266 16 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (246 22 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (231 231 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (231 231 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (231 231 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (211 16 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (208 13 (:DEFINITION NATP))
 (204 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (204 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (169 22 (:REWRITE BVCHOP-IDENTITY))
 (168 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (168 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (162 16 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (157 37 (:REWRITE DEFAULT-+-1))
 (142 142 (:REWRITE BOUND-WHEN-USB2))
 (142 142 (:REWRITE <-WHEN-BVLT))
 (142 142 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (136 16 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (119 3 (:REWRITE DISTRIBUTIVITY))
 (117 117 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (117 117 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (117 117 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (110 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (105 67 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (102 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (102 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (101 10 (:REWRITE DEFAULT-*-2))
 (99 99 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (93 67 (:REWRITE NOT-<-WHEN-SBVLT))
 (87 87 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (87 87 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (87 87 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (87 87 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (87 87 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (71 71 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (70 22 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (70 22 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (67 67 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (67 67 (:REWRITE BOUND-WHEN-USB))
 (67 67 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (67 37 (:REWRITE DEFAULT-+-2))
 (60 60 (:TYPE-PRESCRIPTION NATP))
 (58 58 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (58 58 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (58 58 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (54 3 (:REWRITE FLOOR-WHEN-DIVISIBLE-CHEAP))
 (52 26 (:REWRITE GETBIT-WHEN-NOT-0))
 (47 14 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (44 22 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (44 22 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (44 22 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (42 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (40 3 (:REWRITE *-OF---ARG2))
 (32 32 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (28 28 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (28 28 (:LINEAR EXPT-BOUND-LINEAR))
 (28 28 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (26 26 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (26 26 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (26 26 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (26 26 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (26 26 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-1))
 (22 22 (:TYPE-PRESCRIPTION POSP))
 (22 22 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (22 22 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (22 22 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (22 22 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (22 22 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (22 22 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (22 22 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (22 22 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (22 22 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (16 16 (:REWRITE UBP-LONGER-BETTER))
 (16 16 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (16 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (14 14 (:LINEAR EXPT-BOUND-LINEAR-2))
 (14 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (13 13 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (13 13 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (10 10 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (8 8 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (8 4 (:REWRITE SMALL-INT-HACK))
 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (4 4 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (4 1 (:REWRITE INTEGERP-OF-*))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (3 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE FLOOR-DIVIDE-BY-COMMON-CONSTANT-FACTOR))
 (2 2 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (2 2 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (2 2 (:REWRITE FLOOR-MINUS-ARG2-HACK))
 (2 2 (:REWRITE EQUAL-OF-EXPT2-AND-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (2 2 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (1 1 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (1 1 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (1 1 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (1 1 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (1 1 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NOT-EQUAL-BVCHOP-WHEN-NOT-EQUAL-BVCHOP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 )
(INTEGERP-OF-TIMES-OF-/-OF-EXPT-AND-MINUS-OF-BVCHOP
 (1639 3 (:REWRITE DEFAULT-UNARY-/))
 (985 15 (:LINEAR BVCHOP-UPPER-BOUND))
 (825 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (674 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (584 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (398 1 (:REWRITE EQUAL-OF-0-AND-+-OF---ALT))
 (398 1 (:REWRITE EQUAL-OF-0-AND-+-OF--))
 (374 141 (:REWRITE DEFAULT-<-2))
 (344 141 (:REWRITE DEFAULT-<-1))
 (312 312 (:TYPE-PRESCRIPTION EVENP))
 (300 15 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (243 2 (:REWRITE SMALL-INT-HACK))
 (241 17 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (240 15 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (240 15 (:DEFINITION NATP))
 (208 104 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (208 104 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (208 104 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (198 22 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (198 22 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (180 15 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (165 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (165 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (161 17 (:REWRITE BVCHOP-IDENTITY))
 (150 15 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (141 141 (:REWRITE BOUND-WHEN-USB2))
 (141 141 (:REWRITE <-WHEN-BVLT))
 (141 141 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (119 119 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (119 119 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (119 119 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (106 68 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (104 104 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (104 104 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (104 104 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (100 100 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (99 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (99 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (98 68 (:REWRITE NOT-<-WHEN-SBVLT))
 (95 35 (:REWRITE DEFAULT-+-1))
 (87 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (75 75 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (68 68 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (68 68 (:REWRITE BOUND-WHEN-USB))
 (68 68 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (65 17 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (65 17 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (61 61 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (61 61 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (61 61 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (60 30 (:REWRITE GETBIT-WHEN-NOT-0))
 (49 49 (:TYPE-PRESCRIPTION NATP))
 (44 11 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (42 3 (:REWRITE DEFAULT-*-2))
 (40 35 (:REWRITE DEFAULT-+-2))
 (34 17 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (34 17 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (34 17 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (30 30 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (30 30 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (30 30 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (30 30 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (30 30 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (30 30 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (30 15 (:REWRITE GETBIT-WHEN-NOT-1))
 (28 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (22 22 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (22 22 (:LINEAR EXPT-BOUND-LINEAR))
 (22 22 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (17 17 (:TYPE-PRESCRIPTION POSP))
 (17 17 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (17 17 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (17 17 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (17 17 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (17 17 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (17 17 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (17 17 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (17 17 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (17 17 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (16 16 (:REWRITE UBP-LONGER-BETTER))
 (16 16 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (15 15 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (15 15 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (11 11 (:LINEAR EXPT-BOUND-LINEAR-2))
 (5 2 (:REWRITE INTEGERP-OF-*))
 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (4 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (2 2 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (2 2 (:REWRITE EQUAL-OF-EXPT2-AND-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (2 2 (:REWRITE BVCHOP-EQUAL-EXPT-2-HACK))
 (2 2 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 )
(SLICE-31-2-MINUS-4-ALT
 (1534 10 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (753 10 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (742 32 (:LINEAR <=-OF-LOGTAIL-SAME-LINEAR))
 (650 8 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (419 419 (:TYPE-PRESCRIPTION LOGTAIL-NON-POSITIVE))
 (336 16 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL-STRONG))
 (226 133 (:REWRITE DEFAULT-<-1))
 (136 136 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (136 136 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (136 136 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (135 135 (:REWRITE BOUND-WHEN-USB2))
 (133 133 (:REWRITE DEFAULT-<-2))
 (133 133 (:REWRITE <-WHEN-BVLT))
 (133 133 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (127 127 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (126 126 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (126 126 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (97 97 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (90 9 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (87 87 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (87 87 (:REWRITE UBP-LONGER-BETTER))
 (79 79 (:REWRITE LOGTAIL-WHEN-NOT-POSP-ARG1))
 (79 29 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (79 29 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (72 9 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (56 1 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT))
 (52 52 (:REWRITE LOGTAIL-WHEN-NOT-INTEGERP-ARG2))
 (36 18 (:REWRITE GETBIT-WHEN-NOT-0))
 (33 33 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (33 33 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (33 33 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (33 33 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (33 33 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (33 33 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (31 31 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (29 29 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (29 29 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (29 29 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (29 29 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (29 29 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (28 14 (:REWRITE NOT-<-WHEN-SBVLT))
 (22 9 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (18 18 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (18 18 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (18 18 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (18 18 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (18 18 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (18 9 (:REWRITE GETBIT-WHEN-NOT-1))
 (15 8 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (14 14 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (14 14 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 12 (:REWRITE BOUND-WHEN-USB))
 (11 11 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (11 11 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (11 8 (:REWRITE DEFAULT-+-1))
 (11 5 (:REWRITE BVCHOP-BOUND))
 (7 7 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (5 5 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 1 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVPLUS-TRIM-LEADING-CONSTANT))
 (2 1 (:REWRITE BOOLAND-OF-CONSTANT-ARG2))
 (1 1 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (1 1 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (1 1 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (1 1 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (1 1 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (1 1 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NOT-EQUAL-BVCHOP-WHEN-NOT-EQUAL-BVCHOP))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE-ALT))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (1 1 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (1 1 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (1 1 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (1 1 (:REWRITE BVPLUS-SUBST-VALUE))
 (1 1 (:REWRITE BVCHOP-SUM-SOLVE-FOR-CONSTANT-ARG2))
 (1 1 (:REWRITE BVCHOP-SUM-SOLVE-FOR-CONSTANT-ARG1))
 (1 1 (:REWRITE BVCHOP-REDUCE-WHEN-ALL-BUT-TOP-BIT-KNOWN))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (1 1 (:REWRITE BOOL-FIX-IFF))
 (1 1 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 )
(BVUMINUS-WHEN-SMALLER-BIND-FREE
 (177 177 (:TYPE-PRESCRIPTION EVENP))
 (118 59 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (118 59 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (118 59 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (59 59 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (37 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (37 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (36 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (32 1 (:LINEAR EXPT-HALF-LINEAR))
 (28 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 4 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (23 23 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (18 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE BOUND-WHEN-USB2))
 (14 14 (:REWRITE <-WHEN-BVLT))
 (14 14 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (13 1 (:REWRITE DEFAULT-*-2))
 (12 6 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (9 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (9 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (6 6 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (6 6 (:REWRITE NOT-<-WHEN-SBVLT))
 (6 6 (:REWRITE BOUND-WHEN-USB))
 (6 6 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
