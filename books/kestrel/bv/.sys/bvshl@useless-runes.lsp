(BVSHL)
(BVSHL-OF-0-ARG1
 (4 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 )
(BVSHL-OF-0-ARG2
 (6 2 (:DEFINITION POSP))
 (5 1 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (5 1 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (4 1 (:REWRITE BVCHOP-IDENTITY))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 )
(BVSHL-OF-0-ARG3
 (22 1 (:DEFINITION EXPT))
 (12 3 (:REWRITE BVCHOP-IDENTITY))
 (11 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (10 8 (:REWRITE DEFAULT-<-2))
 (9 8 (:REWRITE DEFAULT-<-1))
 (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (7 2 (:DEFINITION NATP))
 (7 1 (:REWRITE EQUAL-OF-BVCHOP-AND-BVCHOP-SAME))
 (7 1 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (6 2 (:REWRITE DEFAULT-*-2))
 (5 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (4 1 (:DEFINITION POSP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (3 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 )
(BVSHL-OF-BVCHOP
 (82 21 (:REWRITE BVCHOP-IDENTITY))
 (69 57 (:REWRITE DEFAULT-<-1))
 (59 57 (:REWRITE DEFAULT-<-2))
 (48 20 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (48 16 (:REWRITE DEFAULT-*-2))
 (48 10 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (44 44 (:TYPE-PRESCRIPTION NATP))
 (40 37 (:REWRITE DEFAULT-+-2))
 (40 10 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (39 37 (:REWRITE DEFAULT-+-1))
 (39 13 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (38 38 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (32 16 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (28 13 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (21 21 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (21 21 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (21 21 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION POSP))
 (19 19 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (19 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (17 16 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (17 9 (:REWRITE ZIP-OPEN))
 (16 16 (:REWRITE DEFAULT-*-1))
 (13 13 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 4 (:DEFINITION POSP))
 (10 2 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (10 2 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH))
 (4 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (4 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 2 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (3 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP))
 (3 1 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (2 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (2 2 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (2 2 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 )
(INTEGERP-OF-BVSHL)
(NATP-OF-BVSHL)
(UNSIGNED-BYTE-P-OF-BVSHL
 (41 1 (:REWRITE BVCHOP-NOT-0-WHEN-LOW-BIT-NOT-0))
 (34 1 (:REWRITE BVCHOP-NOT-0-WHEN-GETBIT-NOT-0))
 (31 2 (:LINEAR GETBIT-BOUND-LINEAR))
 (20 20 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (12 3 (:REWRITE BVCHOP-IDENTITY))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (8 4 (:REWRITE GETBIT-WHEN-NOT-1))
 (8 4 (:REWRITE GETBIT-WHEN-NOT-0))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (6 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (6 2 (:DEFINITION POSP))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (5 1 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (5 1 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (4 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (4 4 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (4 4 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (4 4 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 2 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (4 2 (:REWRITE GETBIT-IDENTITY))
 (4 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (4 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (1 1 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 )
(BVSHL-REWRITE-WITH-BVCHOP
 (200 8 (:DEFINITION EXPT))
 (66 58 (:REWRITE DEFAULT-+-2))
 (60 20 (:DEFINITION POSP))
 (58 58 (:REWRITE DEFAULT-+-1))
 (55 15 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (55 15 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (48 16 (:REWRITE DEFAULT-*-2))
 (31 31 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:TYPE-PRESCRIPTION POSP))
 (20 15 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (16 16 (:REWRITE DEFAULT-*-1))
 (16 8 (:REWRITE ZIP-OPEN))
 (15 15 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (15 15 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (15 15 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (15 15 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (5 5 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (5 5 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (5 5 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (5 5 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 (4 4 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG4-CONSTANT))
 (4 4 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (4 1 (:REWRITE BVCHOP-IDENTITY))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVSHL-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
 (100 4 (:DEFINITION EXPT))
 (36 32 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE DEFAULT-+-1))
 (30 10 (:DEFINITION POSP))
 (27 7 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (27 7 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (24 8 (:REWRITE DEFAULT-*-2))
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11 (:TYPE-PRESCRIPTION POSP))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 7 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (8 4 (:REWRITE ZIP-OPEN))
 (7 7 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 1 (:REWRITE BVCHOP-IDENTITY))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG4-CONSTANT))
 (2 2 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN-AXE))
 (1 1 (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
 )
(BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT)
(BVSHL-CASES-TERM-FN-AUX
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BVSHL-CASES-TERM-FN)
(BVSHL-16-CASES
 (496 166 (:REWRITE BVCHOP-IDENTITY))
 (464 16 (:DEFINITION EXPT))
 (213 107 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (192 32 (:REWRITE COMMUTATIVITY-OF-+))
 (185 165 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (182 166 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (181 165 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (177 166 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (175 166 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (174 165 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (172 172 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (168 166 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (166 166 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (165 165 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (162 138 (:REWRITE DEFAULT-+-2))
 (152 15 (:LINEAR BVCAT-UPPER-BOUND-LINEAR))
 (141 141 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (138 138 (:REWRITE DEFAULT-+-1))
 (110 106 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (107 107 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (107 1 (:REWRITE BVCHOP-NOT-0-WHEN-LOW-BIT-NOT-0))
 (106 106 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (106 106 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (106 106 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (105 73 (:REWRITE DEFAULT-<-1))
 (102 100 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (100 100 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (100 100 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (100 100 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (100 100 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (96 32 (:REWRITE DEFAULT-*-2))
 (92 92 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (77 13 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (73 73 (:REWRITE DEFAULT-<-2))
 (72 54 (:REWRITE SLICE-OUT-OF-ORDER))
 (67 1 (:REWRITE BVCHOP-NOT-0-WHEN-GETBIT-NOT-0))
 (55 11 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (36 36 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (36 9 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (32 32 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 16 (:REWRITE ZIP-OPEN))
 (28 11 (:REWRITE GETBIT-IDENTITY))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-1))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-0))
 (26 13 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (25 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (25 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (15 15 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (13 13 (:TYPE-PRESCRIPTION POSP))
 (13 13 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (13 13 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (13 13 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (13 13 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (11 11 (:REWRITE GETBIT-IDENTITY-FREE))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:TYPE-PRESCRIPTION BITP))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-LOW))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-HIGH))
 (7 7 (:REWRITE BVCAT-SUBST-1))
 (6 2 (:DEFINITION POSP))
 (5 5 (:DEFINITION BITP))
 (5 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (4 4 (:REWRITE GETBIT-OF-IF-TWO-CONSTANTS))
 (3 3 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (3 3 (:REWRITE SLICE-OF-GETBIT-TOO-HIGH))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 )
(BVSHL-32-CASES
 (1008 342 (:REWRITE BVCHOP-IDENTITY))
 (464 16 (:DEFINITION EXPT))
 (437 219 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (374 342 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (373 341 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (361 341 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (353 342 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (351 342 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (350 341 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (348 348 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (344 342 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (342 342 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (341 341 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (312 31 (:LINEAR BVCAT-UPPER-BOUND-LINEAR))
 (269 269 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (222 218 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (219 219 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (218 218 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (218 218 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (218 218 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (198 196 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (196 196 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (196 196 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (196 196 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (196 196 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (192 32 (:REWRITE COMMUTATIVITY-OF-+))
 (188 188 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (171 1 (:REWRITE BVCHOP-NOT-0-WHEN-LOW-BIT-NOT-0))
 (169 105 (:REWRITE DEFAULT-<-1))
 (162 138 (:REWRITE DEFAULT-+-2))
 (141 13 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (138 138 (:REWRITE DEFAULT-+-1))
 (120 102 (:REWRITE SLICE-OUT-OF-ORDER))
 (105 105 (:REWRITE DEFAULT-<-2))
 (99 1 (:REWRITE BVCHOP-NOT-0-WHEN-GETBIT-NOT-0))
 (96 32 (:REWRITE DEFAULT-*-2))
 (87 11 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (64 64 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (52 52 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (41 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (41 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (36 9 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 16 (:REWRITE ZIP-OPEN))
 (31 31 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (28 11 (:REWRITE GETBIT-IDENTITY))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-1))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-0))
 (26 13 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (13 13 (:TYPE-PRESCRIPTION POSP))
 (13 13 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (13 13 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (13 13 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (13 13 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (11 11 (:REWRITE GETBIT-IDENTITY-FREE))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:TYPE-PRESCRIPTION BITP))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-LOW))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-HIGH))
 (7 7 (:REWRITE BVCAT-SUBST-1))
 (6 2 (:DEFINITION POSP))
 (5 5 (:DEFINITION BITP))
 (5 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (4 4 (:REWRITE GETBIT-OF-IF-TWO-CONSTANTS))
 (3 3 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (3 3 (:REWRITE SLICE-OF-GETBIT-TOO-HIGH))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 )
(BVSHL-64-CASES
 (2032 694 (:REWRITE BVCHOP-IDENTITY))
 (885 443 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (758 694 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (757 693 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (713 693 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (705 694 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (703 694 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (702 693 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (700 700 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (696 694 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (694 694 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (693 693 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (632 63 (:LINEAR BVCAT-UPPER-BOUND-LINEAR))
 (525 525 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (464 16 (:DEFINITION EXPT))
 (446 442 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (443 443 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (442 442 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (442 442 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (442 442 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (390 388 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (388 388 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (388 388 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (388 388 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (388 388 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (380 380 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (299 1 (:REWRITE BVCHOP-NOT-0-WHEN-LOW-BIT-NOT-0))
 (297 169 (:REWRITE DEFAULT-<-1))
 (269 13 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (216 198 (:REWRITE SLICE-OUT-OF-ORDER))
 (192 32 (:REWRITE COMMUTATIVITY-OF-+))
 (169 169 (:REWRITE DEFAULT-<-2))
 (163 1 (:REWRITE BVCHOP-NOT-0-WHEN-GETBIT-NOT-0))
 (162 138 (:REWRITE DEFAULT-+-2))
 (151 11 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (138 138 (:REWRITE DEFAULT-+-1))
 (128 128 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (96 32 (:REWRITE DEFAULT-*-2))
 (84 84 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (73 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (73 9 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (63 63 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (36 9 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 16 (:REWRITE ZIP-OPEN))
 (28 11 (:REWRITE GETBIT-IDENTITY))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-1))
 (26 13 (:REWRITE GETBIT-WHEN-NOT-0))
 (26 13 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (13 13 (:TYPE-PRESCRIPTION POSP))
 (13 13 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (13 13 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (13 13 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (13 13 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (11 11 (:REWRITE GETBIT-IDENTITY-FREE))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:TYPE-PRESCRIPTION BITP))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-LOW))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-HIGH))
 (7 7 (:REWRITE BVCAT-SUBST-1))
 (6 2 (:DEFINITION POSP))
 (5 5 (:DEFINITION BITP))
 (5 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (4 4 (:REWRITE GETBIT-OF-IF-TWO-CONSTANTS))
 (3 3 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (3 3 (:REWRITE SLICE-OF-GETBIT-TOO-HIGH))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 )
