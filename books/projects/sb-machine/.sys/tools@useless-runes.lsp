(TMP-DEFTYPES-SYMBOLP-OF-SYMBOL-FIX)
(SB::GHOST-STATE-P)
(SB::BOOLEANP-OF-SYMBOLP-FOR-GHOST-STATE-P-KEY-LEMMA)
(SB::BOOLEANP-OF-SYMBOLP-FOR-GHOST-STATE-P-KEY)
(SB::TRUE-LISTP-WHEN-GHOST-STATE-P-COMPOUND-RECOGNIZER)
(SB::GHOST-STATE-P-WHEN-NOT-CONSP)
(SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P)
(SB::GHOST-STATE-P-OF-CONS)
(SB::GHOST-STATE-P-OF-REMOVE-ASSOC
 (51 10 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 (16 16 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION SB::BOOLEANP-OF-SYMBOLP-FOR-GHOST-STATE-P-KEY))
 )
(SB::GHOST-STATE-P-OF-PUT-ASSOC)
(SB::GHOST-STATE-P-OF-FAST-ALIST-CLEAN)
(SB::GHOST-STATE-P-OF-HONS-SHRINK-ALIST)
(SB::GHOST-STATE-P-OF-HONS-ACONS)
(SB::ALISTP-WHEN-GHOST-STATE-P-REWRITE)
(SB::ALISTP-WHEN-GHOST-STATE-P)
(SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P)
(SB::GHOST-STATE-FIX$INLINE)
(SB::GHOST-STATE-P-OF-GHOST-STATE-FIX
 (1016 100 (:REWRITE SB::LEN-CONSP))
 (591 38 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (562 24 (:DEFINITION TRUE-LISTP))
 (434 100 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (288 48 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (265 11 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 (236 62 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (166 166 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (158 18 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P))
 (105 7 (:DEFINITION SB::GHOST-STATE-P))
 (102 11 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 (96 96 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (96 48 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (64 12 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-REGISTERS-P))
 (64 12 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-MEMORY-P))
 (56 56 (:REWRITE DEFAULT-CDR))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (48 48 (:REWRITE SET::IN-SET))
 (46 46 (:REWRITE DEFAULT-CAR))
 (40 10 (:REWRITE SB::SB-P-OF-CDR-WHEN-SB-P))
 (16 16 (:REWRITE SB::REGISTERS-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SB::MEMORY-P-WHEN-NOT-CONSP))
 (16 4 (:REWRITE SB::REGISTERS-P-OF-CDR-WHEN-REGISTERS-P))
 (16 4 (:REWRITE SB::MEMORY-P-OF-CDR-WHEN-MEMORY-P))
 )
(SB::GHOST-STATE-FIX-WHEN-GHOST-STATE-P
 (346 41 (:REWRITE SB::LEN-CONSP))
 (242 12 (:DEFINITION TRUE-LISTP))
 (201 21 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 (199 41 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (137 19 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P))
 (126 21 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (87 37 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (66 66 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 44 (:REWRITE DEFAULT-CAR))
 (42 42 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (42 21 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (41 10 (:REWRITE SB::SB-P-OF-CDR-WHEN-SB-P))
 (38 34 (:REWRITE DEFAULT-CDR))
 (21 21 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (21 21 (:REWRITE SET::IN-SET))
 (18 9 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-REGISTERS-P))
 (18 9 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-MEMORY-P))
 (7 7 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 3 (:REWRITE SB::REGISTERS-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SB::MEMORY-P-WHEN-NOT-CONSP))
 )
(SB::GHOST-STATE-FIX$INLINE
 (4 4 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (4 1 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P))
 (4 1 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (1 1 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 )
(SB::GHOST-STATE-EQUIV$INLINE)
(SB::GHOST-STATE-EQUIV-IS-AN-EQUIVALENCE)
(SB::GHOST-STATE-EQUIV-IMPLIES-EQUAL-GHOST-STATE-FIX-1)
(SB::GHOST-STATE-FIX-UNDER-GHOST-STATE-EQUIV)
(SB::EQUAL-OF-GHOST-STATE-FIX-1-FORWARD-TO-GHOST-STATE-EQUIV)
(SB::EQUAL-OF-GHOST-STATE-FIX-2-FORWARD-TO-GHOST-STATE-EQUIV)
(SB::GHOST-STATE-EQUIV-OF-GHOST-STATE-FIX-1-FORWARD)
(SB::GHOST-STATE-EQUIV-OF-GHOST-STATE-FIX-2-FORWARD)
(SB::CONS-OF-SYMBOL-FIX-K-UNDER-GHOST-STATE-EQUIV
 (18 4 (:REWRITE SB::GHOST-STATE-FIX-WHEN-GHOST-STATE-P))
 (9 2 (:REWRITE SB::GHOST-STATE-P-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION SB::GHOST-STATE-P))
 (3 3 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 )
(SB::CONS-SYMBOL-EQUIV-CONGRUENCE-ON-K-UNDER-GHOST-STATE-EQUIV)
(SB::CONS-OF-GHOST-STATE-FIX-Y-UNDER-GHOST-STATE-EQUIV
 (6 2 (:REWRITE SB::GHOST-STATE-P-OF-CONS))
 (4 4 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 )
(SB::CONS-GHOST-STATE-EQUIV-CONGRUENCE-ON-Y-UNDER-GHOST-STATE-EQUIV)
(SB::GHOST-STATE-FIX-OF-ACONS
 (11 3 (:REWRITE SB::GHOST-STATE-FIX-WHEN-GHOST-STATE-P))
 (4 4 (:TYPE-PRESCRIPTION SB::GHOST-STATE-P))
 (4 1 (:REWRITE SB::GHOST-STATE-P-OF-CONS))
 (2 2 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 (2 2 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 )
(SB::GHOST-STATE-FIX-OF-APPEND
 (134 19 (:REWRITE SB::GHOST-STATE-FIX-WHEN-GHOST-STATE-P))
 (53 53 (:TYPE-PRESCRIPTION SB::GHOST-STATE-P))
 (45 27 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (20 5 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 (16 4 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P))
 (16 4 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 (12 1 (:REWRITE SB::GHOST-STATE-P-OF-CONS))
 )
(SB::CONSP-CAR-OF-GHOST-STATE-FIX
 (50 10 (:REWRITE SB::GHOST-STATE-FIX-WHEN-GHOST-STATE-P))
 (27 27 (:TYPE-PRESCRIPTION SB::GHOST-STATE-P))
 (20 5 (:REWRITE SB::GHOST-STATE-P-OF-CDR-WHEN-GHOST-STATE-P))
 (14 14 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (10 2 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 (8 2 (:REWRITE SB::SYMBOLP-OF-CAAR-WHEN-GHOST-STATE-P))
 )
(SB::PUT-ASSOC-GHOST-STATE
 (54 6 (:REWRITE SB::LEN-CONSP))
 (44 1 (:DEFINITION PUT-ASSOC-EQUAL))
 (34 2 (:DEFINITION TRUE-LISTP))
 (33 3 (:REWRITE DEFAULT-CAR))
 (31 1 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (23 6 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (11 11 (:TYPE-PRESCRIPTION SB::SB-P))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 5 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(SB::ASSOC-GHOST-STATE
 (1104 145 (:REWRITE SB::LEN-CONSP))
 (745 70 (:REWRITE DEFAULT-CAR))
 (733 35 (:DEFINITION TRUE-LISTP))
 (619 145 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (420 70 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (329 104 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (217 217 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (160 24 (:REWRITE SB::ASSOC-REGISTERS))
 (140 140 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (140 70 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (106 24 (:REWRITE SB::ASSOC-MEMORY))
 (99 17 (:REWRITE SB::REGISTERS-P-WHEN-NOT-CONSP))
 (70 70 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (70 70 (:REWRITE SET::IN-SET))
 (47 47 (:REWRITE DEFAULT-CDR))
 (45 17 (:REWRITE SB::MEMORY-P-WHEN-NOT-CONSP))
 (12 3 (:REWRITE SB::SB-P-OF-CDR-WHEN-SB-P))
 (12 3 (:REWRITE SB::REGISTERS-P-OF-CDR-WHEN-REGISTERS-P))
 (12 3 (:REWRITE SB::MEMORY-P-OF-CDR-WHEN-MEMORY-P))
 )
(SB::GHOST-STATE-EQLABLE-ALISTP
 (320 56 (:REWRITE SB::LEN-CONSP))
 (211 56 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (202 10 (:DEFINITION TRUE-LISTP))
 (120 20 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (110 33 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (71 6 (:REWRITE SB::LOCKP-IS-ACL2-NUMBERP))
 (68 68 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (60 6 (:REWRITE SB::MEMORY-EQLABLE-ALISTP))
 (48 12 (:REWRITE SB::LOCK-IF-NATP))
 (42 12 (:REWRITE SB::LOCKP-IS-INTEGERP))
 (40 40 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (40 20 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (36 8 (:REWRITE SB::MEMORY-P-WHEN-NOT-CONSP))
 (36 6 (:REWRITE SB::ACL2-NUMBERP-OF-INTEGERP))
 (30 30 (:TYPE-PRESCRIPTION SB::LOCKP))
 (30 6 (:DEFINITION NATP))
 (29 29 (:REWRITE DEFAULT-CAR))
 (20 20 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (20 20 (:REWRITE SET::IN-SET))
 (17 12 (:REWRITE SB::LOCKP-IF-NIL))
 (13 13 (:REWRITE DEFAULT-CDR))
 (8 2 (:REWRITE SB::SB-P-OF-CDR-WHEN-SB-P))
 (8 2 (:REWRITE SB::MEMORY-P-OF-CDR-WHEN-MEMORY-P))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(SB::STORE-BUFFER-PLUS-MEMORY-SB
 (554 94 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (447 94 (:REWRITE SB::LEN-CONSP))
 (280 12 (:DEFINITION TRUE-LISTP))
 (239 21 (:REWRITE DEFAULT-CDR))
 (188 78 (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
 (144 24 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (138 78 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
 (96 2 (:DEFINITION ALISTP))
 (77 77 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (77 17 (:REWRITE SB::ASSOC-REGISTERS))
 (74 4 (:REWRITE SB::MEMORY-P-WHEN-NOT-CONSP))
 (65 17 (:REWRITE SB::ASSOC-GHOST-STATE))
 (52 4 (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
 (48 48 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (48 24 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (36 12 (:REWRITE SB::REGISTERS-P-WHEN-NOT-CONSP))
 (36 6 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (28 4 (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
 (24 24 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (24 24 (:REWRITE SET::IN-SET))
 (8 8 (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
 )
(SB::BOOLEANP-OF-STORE-BUFFER-PLUS-MEMORY-SB)
(SB::SB-DEQ-IND
 (139 4 (:DEFINITION ACL2-COUNT))
 (78 7 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (40 7 (:REWRITE SB::LEN-CONSP))
 (32 8 (:REWRITE DEFAULT-+-2))
 (28 28 (:TYPE-PRESCRIPTION SB::SB-P))
 (24 6 (:REWRITE SB::SB-P-OF-SB-DEQ))
 (22 2 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
 (21 2 (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
 (21 1 (:DEFINITION TRUE-LISTP))
 (17 10 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (16 8 (:REWRITE DEFAULT-+-1))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 2 (:REWRITE SB::SB-LATEST-SB-DEQ))
 (5 2 (:REWRITE SB::NOT-NO-PENDING-LATEST))
 (5 1 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 1 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(SB::STORE-BUFFER-PLUS-MEMORY
 (64 5 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (45 5 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (43 2 (:REWRITE SB::PROC-NUM-<-LEN-NUM-PROCS))
 (32 5 (:REWRITE SB::LEN-CONSP))
 (25 1 (:DEFINITION LEN))
 (17 1 (:DEFINITION TRUE-LISTP))
 (16 6 (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (11 3 (:REWRITE SB::LOCKP-IS-INTEGERP))
 (10 1 (:REWRITE SB::PROC-NUM-<-NUM-PROCS-LEN))
 (8 6 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
 (8 5 (:REWRITE DEFAULT-<-2))
 (7 1 (:REWRITE SB::LOCK-IF-NATP))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 2 (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
 (4 4 (:TYPE-PRESCRIPTION SB::LOCKP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE SB::LOCKP-IF-NIL))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(SB::BOOLEANP-OF-STORE-BUFFER-PLUS-MEMORY)
(SB::WRITE-SB-STORE-BUFFER-PLUS-MEMORY
 (414 24 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (264 60 (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
 (191 17 (:REWRITE DEFAULT-CDR))
 (148 24 (:REWRITE SB::LEN-CONSP))
 (140 60 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
 (87 3 (:DEFINITION TRUE-LISTP))
 (60 30 (:REWRITE SB::SB-LATEST-SB-NEXT-FLUSH))
 (55 11 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (50 2 (:DEFINITION LEN))
 (48 4 (:REWRITE SB::ASSOC-REGISTERS))
 (46 4 (:REWRITE SB::ASSOC-GHOST-STATE))
 (43 2 (:REWRITE SB::PROC-NUM-<-LEN-NUM-PROCS))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (32 2 (:REWRITE SB::GHOST-STATE-P-WHEN-NOT-CONSP))
 (24 6 (:REWRITE SB::READ-SB-NO-PENDING-2))
 (24 4 (:REWRITE SB::REGISTERS-P-WHEN-NOT-CONSP))
 (22 5 (:REWRITE SB::LOCKP-IS-INTEGERP))
 (20 4 (:REWRITE SB::ASSOC-MEMORY))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 2 (:REWRITE SB::LOCK-IF-NATP))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:TYPE-PRESCRIPTION SB::NO-PENDING))
 (12 6 (:REWRITE SB::READ-SB-NO-PENDING))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (10 8 (:REWRITE DEFAULT-CAR))
 (10 7 (:REWRITE DEFAULT-<-2))
 (8 8 (:TYPE-PRESCRIPTION SB::REGISTERS-P))
 (7 7 (:TYPE-PRESCRIPTION SB::LOCKP))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION SB::READ-SB))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (4 4 (:TYPE-PRESCRIPTION SB::GHOST-STATE-P))
 (4 4 (:REWRITE SB::CONSP-WHEN-NOT-NO-PENDING))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE SB::LOCKP-IF-NIL))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(SB::PHASE-MACHINE-STORE-BUFFER-PLUS-MEMORY
 (121 6 (:REWRITE SB::PROC-NUM-<-LEN-NUM-PROCS))
 (100 4 (:DEFINITION LEN))
 (94 10 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
 (72 12 (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
 (72 12 (:REWRITE SB::LEN-CONSP))
 (34 2 (:DEFINITION TRUE-LISTP))
 (33 9 (:REWRITE SB::LOCKP-IS-INTEGERP))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (21 3 (:REWRITE SB::LOCK-IF-NATP))
 (19 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SB::LOCKP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE SB::LOCKP-IF-NIL))
 )
