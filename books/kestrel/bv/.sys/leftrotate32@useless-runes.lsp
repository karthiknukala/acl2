(LEFTROTATE32)
(LEFTROTATE32-OF-0-ARG1)
(LEFTROTATE32-OF-0-ARG2)
(LEFTROTATE-32-OF-BVCHOP-5
 (11 1 (:REWRITE MOD-WHEN-MULTIPLE))
 (11 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-*))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE MOD-WHEN-<))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-WHEN-<-OF-0))
 )
(LEFTROTATE32-OF-BVCHOP-5
 (4 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(UNSIGNED-BYTE-P-32-OF-LEFTROTATE32
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 )
(UNSIGNED-BYTE-P-OF-LEFTROTATE32
 (255 2 (:DEFINITION POSP))
 (249 3 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (242 22 (:REWRITE MOD-WHEN-MULTIPLE))
 (242 22 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (228 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (210 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (176 44 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (137 4 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (132 44 (:REWRITE COMMUTATIVITY-OF-*))
 (128 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (126 1 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (88 88 (:REWRITE DEFAULT-*-2))
 (88 88 (:REWRITE DEFAULT-*-1))
 (66 22 (:REWRITE MOD-WHEN-<))
 (52 37 (:REWRITE DEFAULT-<-2))
 (44 44 (:REWRITE INTEGERP-OF-*))
 (40 10 (:REWRITE DEFAULT-+-2))
 (38 37 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (22 22 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (22 22 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (22 22 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (22 22 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (22 22 (:REWRITE MOD-WHEN-<-OF-0))
 (19 10 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (12 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (7 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (7 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (6 4 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (6 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (5 5 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (5 5 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (4 2 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (4 1 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (3 3 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (3 3 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (3 3 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 (3 2 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (2 2 (:TYPE-PRESCRIPTION SLICE))
 (2 2 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (1 1 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BVCHOP-OF-LEFTROTATE32-DOES-NOTHING
 (48 4 (:DEFINITION EXPT))
 (28 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (18 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (14 10 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE DEFAULT-*-2))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (11 11 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (11 11 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (10 10 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-*-1))
 )
(LEFTROTATE32-OF-BVCHOP-ARG2
 (1077 15 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (695 69 (:REWRITE MOD-WHEN-MULTIPLE))
 (695 69 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (438 26 (:DEFINITION EXPT))
 (436 136 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (408 136 (:REWRITE COMMUTATIVITY-OF-*))
 (392 298 (:REWRITE DEFAULT-*-2))
 (298 298 (:REWRITE DEFAULT-*-1))
 (255 2 (:DEFINITION POSP))
 (243 103 (:REWRITE DEFAULT-+-2))
 (222 97 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (206 53 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (205 69 (:REWRITE MOD-WHEN-<))
 (202 202 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (180 23 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (174 141 (:REWRITE DEFAULT-<-2))
 (169 141 (:REWRITE DEFAULT-<-1))
 (162 26 (:REWRITE COMMUTATIVITY-OF-+))
 (152 152 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (150 150 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (140 7 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (136 136 (:REWRITE INTEGERP-OF-*))
 (120 100 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (120 100 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (118 100 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (115 103 (:REWRITE DEFAULT-+-1))
 (113 97 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (112 97 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (109 97 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (100 100 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (69 69 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (69 69 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (69 69 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (69 69 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (69 69 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (69 69 (:REWRITE MOD-WHEN-<-OF-0))
 (32 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (23 8 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (15 15 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (15 15 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (15 15 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (15 15 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (15 3 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (9 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (8 8 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (8 8 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (7 7 (:TYPE-PRESCRIPTION POSP))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (6 3 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (4 4 (:REWRITE EQUAL-OF-BVCHOP-AND-BVCHOP-WHEN-SMALLER-BVCHOPS-EQUAL))
 (4 4 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (4 4 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (3 3 (:TYPE-PRESCRIPTION SLICE))
 (3 3 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 )
(LEFTROTATE32-OF-BVCHOP
 (23 6 (:REWRITE BVCHOP-IDENTITY))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (7 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (6 6 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (6 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (6 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (5 5 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (5 5 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (5 5 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (5 5 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(LEFTROTATE32-OF-MOD
 (11 1 (:REWRITE MOD-WHEN-MULTIPLE))
 (11 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-*))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE MOD-WHEN-<))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-WHEN-<-OF-0))
 )
(LEFTROTATE-BECOMES-LEFTROTATE32)
(LEFTROTATE32-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT
 (255 2 (:DEFINITION POSP))
 (254 24 (:REWRITE MOD-WHEN-MULTIPLE))
 (254 24 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (252 6 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (228 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (210 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (184 46 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (141 8 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (138 46 (:REWRITE COMMUTATIVITY-OF-*))
 (131 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (126 1 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (92 92 (:REWRITE DEFAULT-*-2))
 (92 92 (:REWRITE DEFAULT-*-1))
 (70 24 (:REWRITE MOD-WHEN-<))
 (48 12 (:REWRITE DEFAULT-+-2))
 (47 32 (:REWRITE DEFAULT-<-2))
 (46 46 (:REWRITE INTEGERP-OF-*))
 (33 32 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (24 24 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (24 24 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (24 24 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (24 24 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (24 24 (:REWRITE MOD-WHEN-<-OF-0))
 (24 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (14 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (14 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (10 10 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (10 10 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (10 10 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (10 8 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (10 4 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (8 8 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (8 4 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (6 6 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (6 6 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (6 6 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (6 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (6 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (6 6 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (6 6 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 (6 4 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (5 2 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (4 4 (:TYPE-PRESCRIPTION SLICE))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (2 2 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(SLICE-OF-LEFTROTATE32-HIGH
 (132 4 (:DEFINITION EXPT))
 (107 99 (:REWRITE DEFAULT-+-2))
 (99 99 (:REWRITE DEFAULT-+-1))
 (83 13 (:REWRITE MOD-WHEN-MULTIPLE))
 (83 13 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (56 14 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (52 36 (:REWRITE DEFAULT-*-2))
 (51 12 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (43 43 (:REWRITE DEFAULT-<-2))
 (43 43 (:REWRITE DEFAULT-<-1))
 (42 14 (:REWRITE COMMUTATIVITY-OF-*))
 (36 36 (:REWRITE DEFAULT-*-1))
 (36 14 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (34 13 (:REWRITE SLICE-OUT-OF-ORDER))
 (21 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (14 14 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (14 14 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (14 14 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (14 14 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (14 14 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (14 14 (:REWRITE INTEGERP-OF-*))
 (14 12 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (14 12 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (13 13 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (13 13 (:REWRITE MOD-WHEN-<-OF-0))
 (12 4 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (9 3 (:REWRITE +-OF---AND-0))
 (8 4 (:REWRITE ZIP-OPEN))
 (8 4 (:REWRITE UNICITY-OF-0))
 (8 2 (:REWRITE BVCHOP-IDENTITY))
 (6 2 (:REWRITE UNSIGNED-BYTE-P-OF-LEFTROTATE))
 (6 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (6 2 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (6 2 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (6 2 (:DEFINITION POSP))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 2 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (3 2 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (2 2 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 )
(BVCHOP-OF-LEFTROTATE32-BOTH
 (98 96 (:REWRITE DEFAULT-+-2))
 (96 96 (:REWRITE DEFAULT-+-1))
 (67 67 (:REWRITE DEFAULT-<-2))
 (67 67 (:REWRITE DEFAULT-<-1))
 (56 14 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (56 14 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (42 14 (:REWRITE SLICE-OUT-OF-ORDER))
 (42 14 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (42 14 (:DEFINITION POSP))
 (35 7 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (35 7 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (26 2 (:DEFINITION EXPT))
 (22 22 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (20 20 (:TYPE-PRESCRIPTION POSP))
 (18 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (14 14 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (14 14 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (14 14 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (14 14 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (14 14 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (14 14 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (14 7 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (12 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (12 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (8 8 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (7 7 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (7 7 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (6 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(SLICE-OF-LEFTROTATE32
 (1249 13 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (1046 135 (:REWRITE MOD-WHEN-MULTIPLE))
 (1046 135 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (1034 37 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (956 34 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (938 34 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (714 238 (:REWRITE COMMUTATIVITY-OF-*))
 (688 13 (:REWRITE SLICE-OUT-OF-ORDER))
 (579 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH))
 (546 5 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (504 6 (:DEFINITION POSP))
 (482 478 (:REWRITE DEFAULT-*-2))
 (478 478 (:REWRITE DEFAULT-*-1))
 (394 238 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (373 135 (:REWRITE MOD-WHEN-<))
 (258 3 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (258 3 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (252 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (252 3 (:REWRITE +-OF---AND-0))
 (238 238 (:REWRITE INTEGERP-OF-*))
 (207 171 (:REWRITE DEFAULT-<-2))
 (180 171 (:REWRITE DEFAULT-<-1))
 (135 135 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (135 135 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (135 135 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (135 135 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (135 135 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (135 135 (:REWRITE MOD-WHEN-<-OF-0))
 (107 87 (:REWRITE DEFAULT-+-2))
 (87 87 (:REWRITE DEFAULT-+-1))
 (50 11 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (43 25 (:REWRITE DEFAULT-UNARY-MINUS))
 (33 1 (:DEFINITION EXPT))
 (27 3 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (27 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (13 13 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (13 13 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (13 13 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (13 13 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (13 11 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (13 11 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (12 12 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 3 (:REWRITE BVCHOP-IDENTITY))
 (9 9 (:TYPE-PRESCRIPTION POSP))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (6 3 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (6 3 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (6 2 (:REWRITE UNSIGNED-BYTE-P-OF-LEFTROTATE))
 (3 3 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (3 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (3 3 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (3 3 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (3 3 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (2 1 (:REWRITE ZIP-OPEN))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:DEFINITION FIX))
 )
(EQUAL-OF-LEFTROTATE32-AND-LEFTROTATE32
 (10 4 (:REWRITE BVCHOP-IDENTITY))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (4 4 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (4 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-AND-BVCHOP-WHEN-SMALLER-BVCHOPS-EQUAL))
 (2 2 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (2 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(GETBIT-OF-LEFTROTATE32-LOW
 (280 8 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (144 8 (:DEFINITION EXPT))
 (84 84 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE DEFAULT-+-1))
 (75 59 (:REWRITE DEFAULT-<-2))
 (59 59 (:REWRITE DEFAULT-<-1))
 (57 41 (:REWRITE FOLD-CONSTS-IN-+))
 (40 40 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (40 40 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (39 9 (:REWRITE MOD-WHEN-MULTIPLE))
 (39 9 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (36 20 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (24 8 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (24 8 (:REWRITE SLICE-OUT-OF-ORDER))
 (24 6 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (20 20 (:REWRITE DEFAULT-*-1))
 (18 6 (:REWRITE COMMUTATIVITY-OF-*))
 (16 8 (:REWRITE ZIP-OPEN))
 (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-1))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-0))
 (12 6 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (12 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (9 9 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (9 9 (:REWRITE MOD-WHEN-<-OF-0))
 (9 6 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (8 8 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (8 8 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (8 8 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (8 8 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (8 8 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (6 6 (:REWRITE INTEGERP-OF-*))
 (6 6 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (6 6 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (6 6 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (3 3 (:TYPE-PRESCRIPTION LEFTROTATE32))
 )
(GETBIT-OF-LEFTROTATE32-HIGH
 (56 56 (:REWRITE DEFAULT-+-2))
 (56 56 (:REWRITE DEFAULT-+-1))
 (43 43 (:REWRITE DEFAULT-<-2))
 (43 43 (:REWRITE DEFAULT-<-1))
 (42 12 (:REWRITE MOD-WHEN-MULTIPLE))
 (42 12 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (40 10 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (40 10 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (40 10 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (39 13 (:REWRITE +-OF---AND-0))
 (30 10 (:REWRITE SLICE-OUT-OF-ORDER))
 (30 10 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (24 6 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (18 6 (:REWRITE COMMUTATIVITY-OF-*))
 (15 15 (:REWRITE DEFAULT-UNARY-MINUS))
 (15 6 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (12 12 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (12 12 (:REWRITE MOD-WHEN-<-OF-0))
 (12 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-1))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-0))
 (12 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (11 11 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (10 10 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (10 10 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (10 10 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (10 10 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (10 10 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (10 10 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (9 6 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (6 6 (:REWRITE INTEGERP-OF-*))
 (6 6 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (6 6 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (6 6 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (3 3 (:TYPE-PRESCRIPTION LEFTROTATE32))
 (3 3 (:REWRITE GETBIT-OF-LEFTROTATE32-LOW))
 )
(GETBIT-OF-LEFTROTATE32
 (1327 11 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (504 4 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (480 48 (:REWRITE MOD-WHEN-MULTIPLE))
 (480 48 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (408 12 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (408 12 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (384 12 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (288 96 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (288 96 (:REWRITE COMMUTATIVITY-OF-*))
 (192 192 (:REWRITE DEFAULT-*-2))
 (192 192 (:REWRITE DEFAULT-*-1))
 (144 48 (:REWRITE MOD-WHEN-<))
 (96 96 (:REWRITE INTEGERP-OF-*))
 (90 66 (:REWRITE DEFAULT-<-2))
 (66 66 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (48 48 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (48 48 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (48 48 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (48 48 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (48 48 (:REWRITE MOD-WHEN-<-OF-0))
 (28 16 (:REWRITE DEFAULT-+-2))
 (23 11 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (22 11 (:REWRITE GETBIT-WHEN-NOT-1))
 (22 11 (:REWRITE GETBIT-WHEN-NOT-0))
 (22 11 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (20 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-+-1))
 (14 11 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (11 11 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (11 11 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION LEFTROTATE))
 )
(GETBIT-OF-LEFTROTATE32-SIMPLE
 (99 9 (:REWRITE MOD-WHEN-MULTIPLE))
 (99 9 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (72 18 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (54 18 (:REWRITE COMMUTATIVITY-OF-*))
 (36 36 (:REWRITE DEFAULT-*-2))
 (36 36 (:REWRITE DEFAULT-*-1))
 (31 11 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (22 11 (:REWRITE GETBIT-WHEN-NOT-1))
 (22 11 (:REWRITE GETBIT-WHEN-NOT-0))
 (22 11 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (18 18 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (18 18 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (18 18 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (18 18 (:REWRITE INTEGERP-OF-*))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (14 11 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (12 4 (:REWRITE +-OF---AND-0))
 (11 11 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (11 11 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (11 11 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (9 9 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (9 9 (:REWRITE MOD-WHEN-<-OF-0))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION LEFTROTATE))
 )
