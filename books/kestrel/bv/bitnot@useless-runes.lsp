(BITNOT)
(BITNOT-TYPE)
(INTEGERP-OF-BITNOT)
(NATP-OF-BITNOT)
(BITNOT-OF-BITNOT
 (64 2 (:LINEAR GETBIT-BOUND-LINEAR))
 (52 4 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (36 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (28 4 (:REWRITE GETBIT-IDENTITY))
 (16 4 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (8 8 (:REWRITE UBP-LONGER-BETTER))
 (8 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (5 5 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (5 5 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (5 5 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE GETBIT-IDENTITY-FREE))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BITNOT-OF-GETBIT-0
 (17 3 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (13 1 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (9 3 (:REWRITE GETBIT-IDENTITY))
 (9 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (6 3 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (4 3 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 1 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (3 3 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (3 3 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (3 3 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (2 2 (:REWRITE UBP-LONGER-BETTER))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(GETBIT-0-OF-BITNOT
 (26 2 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (18 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (14 2 (:REWRITE GETBIT-IDENTITY))
 (14 2 (:LINEAR GETBIT-BOUND-LINEAR))
 (8 2 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (5 5 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (5 5 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (4 4 (:REWRITE UBP-LONGER-BETTER))
 (4 2 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(UNSIGNED-BYTE-P-OF-BITNOT
 (15 1 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (13 1 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (10 3 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (7 1 (:REWRITE GETBIT-IDENTITY))
 (5 2 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (3 3 (:REWRITE UBP-LONGER-BETTER))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (1 1 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (1 1 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (1 1 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(BITNOT-EQUAL-0-REWRITE
 (30 2 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (26 2 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (18 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (14 2 (:REWRITE GETBIT-IDENTITY))
 (8 2 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (4 4 (:REWRITE UBP-LONGER-BETTER))
 (4 2 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (2 2 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (2 2 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(EQUAL-OF-1-AND-BITNOT
 (30 2 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (26 2 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (18 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (14 2 (:REWRITE GETBIT-IDENTITY))
 (8 2 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (4 4 (:REWRITE UBP-LONGER-BETTER))
 (4 2 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (2 2 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (2 2 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(UNSIGNED-BYTE-P-1-OF-BITNOT)
(BITP-OF-BITNOT)
(EQUAL-OF-BITNOT-AND-BITNOT
 (60 4 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (52 4 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (36 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (28 4 (:REWRITE GETBIT-IDENTITY))
 (16 4 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (8 8 (:REWRITE UBP-LONGER-BETTER))
 (8 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (4 4 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (4 4 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 4 (:REWRITE GETBIT-IDENTITY-FREE))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(BITNOT-BECOMES-SUBTRACT)
(GETBIT-OF-1-AND-+-OF-2
 (744 21 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (728 94 (:LINEAR <=-OF-LOGTAIL-SAME-LINEAR))
 (636 94 (:DEFINITION NATP))
 (518 518 (:TYPE-PRESCRIPTION LOGTAIL-NON-POSITIVE))
 (429 21 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (404 12 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (382 230 (:REWRITE DEFAULT-<-1))
 (230 230 (:REWRITE DEFAULT-<-2))
 (130 130 (:TYPE-PRESCRIPTION NATP))
 (110 10 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL-STRONG))
 (106 106 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (106 106 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (99 99 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (74 4 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (62 6 (:REWRITE LOGTAIL-BECOMES-0))
 (48 48 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (39 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (39 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (28 14 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (27 27 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (27 27 (:REWRITE UBP-LONGER-BETTER))
 (27 3 (:REWRITE LOGTAIL-OF-SUM2))
 (24 24 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (20 5 (:REWRITE LOGTAIL-NON-NEG))
 (16 6 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (13 13 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (10 10 (:DEFINITION IFIX))
 (9 9 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (9 3 (:REWRITE COMMUTATIVITY-OF-*))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (6 6 (:REWRITE LOGTAIL-WHEN-NOT-POSP-ARG1))
 (6 6 (:REWRITE LOGTAIL-WHEN-NOT-INTEGERP-ARG2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (4 4 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (4 4 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (4 4 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (4 4 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (4 4 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (4 4 (:REWRITE SLICE-OUT-OF-ORDER))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (4 4 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (4 4 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (3 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )