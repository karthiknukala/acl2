(YUL::RENAMINGP
 (48 12 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (48 12 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (24 24 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(YUL::CONSP-WHEN-RENAMINGP)
(YUL::RENAMING-FIX$INLINE)
(YUL::RENAMINGP-OF-RENAMING-FIX
 (30 10 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (20 20 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALISTP))
 )
(YUL::RENAMING-FIX-WHEN-RENAMINGP
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::RENAMING-FIX$INLINE
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(YUL::RENAMING-EQUIV$INLINE)
(YUL::RENAMING-EQUIV-IS-AN-EQUIVALENCE)
(YUL::RENAMING-EQUIV-IMPLIES-EQUAL-RENAMING-FIX-1)
(YUL::RENAMING-FIX-UNDER-RENAMING-EQUIV)
(YUL::EQUAL-OF-RENAMING-FIX-1-FORWARD-TO-RENAMING-EQUIV)
(YUL::EQUAL-OF-RENAMING-FIX-2-FORWARD-TO-RENAMING-EQUIV)
(YUL::RENAMING-EQUIV-OF-RENAMING-FIX-1-FORWARD)
(YUL::RENAMING-EQUIV-OF-RENAMING-FIX-2-FORWARD)
(YUL::RENAMING->LIST$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:DEFINITION STRIP-CARS))
 )
(YUL::IDENTIFIER-IDENTIFIER-ALISTP-OF-RENAMING->LIST
 (15 5 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (9 3 (:DEFINITION STRIP-CARS))
 (6 6 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX$INLINE))
 )
(YUL::RENAMING->LIST$INLINE-OF-RENAMING-FIX-X
 (126 42 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (103 47 (:DEFINITION STRIP-CARS))
 (84 84 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING->LIST$INLINE-RENAMING-EQUIV-CONGRUENCE-ON-X)
(YUL::RENAMING
 (2 2 (:DEFINITION STRIP-CARS))
 (2 2 (:DEFINITION ALISTP))
 )
(YUL::RENAMINGP-OF-RENAMING
 (57 19 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 )
(YUL::RENAMING->LIST-OF-RENAMING
 (103 47 (:DEFINITION STRIP-CARS))
 )
(YUL::RENAMING-REQUIREMENTS
 (36 12 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (24 24 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALISTP))
 (16 16 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX$INLINE))
 )
(YUL::RENAMING-OF-FIELDS
 (42 14 (:DEFINITION STRIP-CARS))
 (7 7 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (7 7 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING-FIX-WHEN-RENAMING
 (91 13 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (42 14 (:DEFINITION STRIP-CARS))
 (7 7 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::EQUAL-OF-RENAMING
 (18 18 (:DEFINITION STRIP-CARS))
 (14 14 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (12 12 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 )
(YUL::RENAMING-OF-IDENTIFIER-IDENTIFIER-ALIST-FIX-LIST
 (6 2 (:DEFINITION STRIP-CARS))
 )
(YUL::RENAMING-IDENTIFIER-IDENTIFIER-ALIST-EQUIV-CONGRUENCE-ON-LIST)
(YUL::RENAMING-FIX-REDEF)
(YUL::ALISTP-OF-RENAMING->LIST)
(YUL::RENAMING-RESULTP)
(YUL::CONSP-WHEN-RENAMING-RESULTP)
(YUL::RENAMING-RESULT-KIND$INLINE)
(YUL::RENAMING-RESULT-KIND-POSSIBILITIES)
(YUL::RENAMING-RESULT-FIX$INLINE)
(YUL::RENAMING-RESULTP-OF-RENAMING-RESULT-FIX
 (23 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (21 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (17 17 (:TYPE-PRESCRIPTION STRIP-CARS))
 (9 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP
 (9 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(YUL::RENAMING-RESULT-FIX$INLINE
 (170 10 (:DEFINITION MEMBER-EQUAL))
 (140 20 (:REWRITE SUBSETP-CAR-MEMBER))
 (66 66 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE DEFAULT-CAR))
 (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (24 6 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (21 3 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-OF-CDR-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (20 20 (:REWRITE SUBSETP-TRANS2))
 (20 20 (:REWRITE SUBSETP-TRANS))
 (20 20 (:REWRITE SUBSETP-MEMBER . 4))
 (20 20 (:REWRITE SUBSETP-MEMBER . 3))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (20 20 (:REWRITE MEMBER-WHEN-ATOM))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 3))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 2))
 (20 5 (:DEFINITION STRIP-CDRS))
 (12 12 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (12 12 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-SUBSETP-EQUAL))
 (10 10 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (6 6 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(YUL::RENAMING-RESULT-EQUIV$INLINE)
(YUL::RENAMING-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(YUL::RENAMING-RESULT-EQUIV-IMPLIES-EQUAL-RENAMING-RESULT-FIX-1)
(YUL::RENAMING-RESULT-FIX-UNDER-RENAMING-RESULT-EQUIV)
(YUL::EQUAL-OF-RENAMING-RESULT-FIX-1-FORWARD-TO-RENAMING-RESULT-EQUIV)
(YUL::EQUAL-OF-RENAMING-RESULT-FIX-2-FORWARD-TO-RENAMING-RESULT-EQUIV)
(YUL::RENAMING-RESULT-EQUIV-OF-RENAMING-RESULT-FIX-1-FORWARD)
(YUL::RENAMING-RESULT-EQUIV-OF-RENAMING-RESULT-FIX-2-FORWARD)
(YUL::RENAMING-RESULT-KIND$INLINE-OF-RENAMING-RESULT-FIX-X
 (25 16 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (6 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (6 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (5 1 (:DEFINITION FTY::RESERRP))
 (1 1 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 )
(YUL::RENAMING-RESULT-KIND$INLINE-RENAMING-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::CONSP-OF-RENAMING-RESULT-FIX)
(YUL::RENAMING-RESULT-OK->GET$INLINE
 (170 10 (:DEFINITION MEMBER-EQUAL))
 (140 20 (:REWRITE SUBSETP-CAR-MEMBER))
 (66 66 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE DEFAULT-CAR))
 (49 13 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (24 6 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (21 3 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-OF-CDR-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (20 20 (:REWRITE SUBSETP-TRANS2))
 (20 20 (:REWRITE SUBSETP-TRANS))
 (20 20 (:REWRITE SUBSETP-MEMBER . 4))
 (20 20 (:REWRITE SUBSETP-MEMBER . 3))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (20 20 (:REWRITE MEMBER-WHEN-ATOM))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 3))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 2))
 (20 5 (:DEFINITION STRIP-CDRS))
 (12 12 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (12 12 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-SUBSETP-EQUAL))
 (10 10 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (6 6 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 )
(YUL::RENAMINGP-OF-RENAMING-RESULT-OK->GET
 (195 5 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (24 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(YUL::RENAMING-RESULT-OK->GET$INLINE-OF-RENAMING-RESULT-FIX-X
 (96 32 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (79 22 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (64 64 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 (14 14 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULT-FIX$INLINE))
 (14 14 (:TYPE-PRESCRIPTION YUL::CONSP-OF-RENAMING-RESULT-FIX))
 (11 11 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 )
(YUL::RENAMING-RESULT-OK->GET$INLINE-RENAMING-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::RENAMING-RESULT-OK->GET-WHEN-WRONG-KIND
 (7 3 (:DEFINITION STRIP-CARS))
 (5 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (3 1 (:DEFINITION YUL::RENAMINGP))
 (1 1 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::RENAMING-RESULT-OK
 (170 10 (:DEFINITION MEMBER-EQUAL))
 (140 20 (:REWRITE SUBSETP-CAR-MEMBER))
 (68 32 (:DEFINITION STRIP-CARS))
 (66 66 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE DEFAULT-CAR))
 (49 13 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (30 12 (:DEFINITION ALISTP))
 (24 6 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (21 3 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-OF-CDR-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (20 20 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (20 20 (:REWRITE SUBSETP-TRANS2))
 (20 20 (:REWRITE SUBSETP-TRANS))
 (20 20 (:REWRITE SUBSETP-MEMBER . 4))
 (20 20 (:REWRITE SUBSETP-MEMBER . 3))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (20 20 (:REWRITE MEMBER-WHEN-ATOM))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 3))
 (20 20 (:REWRITE INTERSECTP-MEMBER . 2))
 (20 5 (:DEFINITION STRIP-CDRS))
 (12 12 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (12 12 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-SUBSETP-EQUAL))
 (10 10 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (6 6 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 )
(YUL::RETURN-TYPE-OF-RENAMING-RESULT-OK)
(YUL::RENAMING-RESULT-OK->GET-OF-RENAMING-RESULT-OK
 (164 55 (:DEFINITION STRIP-CARS))
 (130 37 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (37 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (35 1 (:DEFINITION YUL::RENAMINGP))
 (26 26 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (14 14 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULT-OK))
 (12 1 (:DEFINITION ALISTP))
 (7 7 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALISTP))
 (1 1 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING-RESULT-OK-OF-FIELDS
 (76 28 (:DEFINITION STRIP-CARS))
 (62 20 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (46 2 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (42 2 (:DEFINITION YUL::RENAMINGP))
 (14 14 (:TYPE-PRESCRIPTION STRIP-CARS))
 (14 14 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 2 (:DEFINITION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALISTP))
 (3 1 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 )
(YUL::RENAMING-RESULT-FIX-WHEN-OK
 (102 21 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (74 26 (:DEFINITION STRIP-CARS))
 (24 2 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (21 1 (:DEFINITION YUL::RENAMINGP))
 (14 14 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (7 7 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 1 (:DEFINITION ALISTP))
 (3 1 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALISTP))
 (1 1 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::EQUAL-OF-RENAMING-RESULT-OK
 (1236 14 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (1214 14 (:DEFINITION YUL::RENAMINGP))
 (608 32 (:DEFINITION MEMBER-EQUAL))
 (448 64 (:REWRITE SUBSETP-CAR-MEMBER))
 (314 185 (:REWRITE DEFAULT-CAR))
 (291 61 (:DEFINITION STRIP-CARS))
 (285 182 (:REWRITE DEFAULT-CDR))
 (235 16 (:REWRITE YUL::CONSP-CAR-OF-IDENTIFIER-IDENTIFIER-ALIST-FIX))
 (172 15 (:DEFINITION STRIP-CDRS))
 (169 31 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-OF-CDR-WHEN-IDENTIFIER-IDENTIFIER-ALISTP))
 (128 128 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (112 112 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-SUBSETP-EQUAL))
 (86 14 (:DEFINITION ALISTP))
 (74 56 (:REWRITE YUL::IDENTIFIER-IDENTIFIER-ALISTP-WHEN-NOT-CONSP))
 (69 43 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (64 64 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (64 64 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (64 64 (:REWRITE SUBSETP-TRANS2))
 (64 64 (:REWRITE SUBSETP-TRANS))
 (64 64 (:REWRITE SUBSETP-MEMBER . 4))
 (64 64 (:REWRITE SUBSETP-MEMBER . 3))
 (64 64 (:REWRITE SUBSETP-MEMBER . 2))
 (64 64 (:REWRITE SUBSETP-MEMBER . 1))
 (64 64 (:REWRITE MEMBER-WHEN-ATOM))
 (64 64 (:REWRITE INTERSECTP-MEMBER . 3))
 (64 64 (:REWRITE INTERSECTP-MEMBER . 2))
 (64 16 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (32 32 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (32 32 (:TYPE-PRESCRIPTION ALISTP))
 (32 32 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (25 25 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (16 16 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING-RESULT-OK-OF-RENAMING-FIX-GET
 (72 24 (:DEFINITION STRIP-CARS))
 (54 18 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (14 14 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 )
(YUL::RENAMING-RESULT-OK-RENAMING-EQUIV-CONGRUENCE-ON-GET)
(YUL::RENAMING-RESULT-ERR->GET$INLINE
 (13 13 (:DEFINITION STRIP-CARS))
 )
(YUL::RESERRP-OF-RENAMING-RESULT-ERR->GET
 (93 3 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (15 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(YUL::RENAMING-RESULT-ERR->GET$INLINE-OF-RENAMING-RESULT-FIX-X
 (194 9 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (176 9 (:DEFINITION FTY::RESERRP))
 (140 29 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (36 36 (:TYPE-PRESCRIPTION ALISTP))
 (28 10 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (27 1 (:REWRITE YUL::RENAMING-FIX-WHEN-RENAMINGP))
 (18 18 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 (9 9 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (4 4 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (2 2 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-IDENTIFIER-ALIST-FIX$INLINE))
 (1 1 (:TYPE-PRESCRIPTION YUL::RENAMINGP))
 )
(YUL::RENAMING-RESULT-ERR->GET$INLINE-RENAMING-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::RENAMING-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION FTY::RESERRP))
 )
(YUL::RENAMING-RESULT-ERR
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::RETURN-TYPE-OF-RENAMING-RESULT-ERR)
(YUL::RENAMING-RESULT-ERR->GET-OF-RENAMING-RESULT-ERR
 (50 8 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (36 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (34 1 (:DEFINITION FTY::RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (9 1 (:DEFINITION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 )
(YUL::RENAMING-RESULT-ERR-OF-FIELDS
 (42 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (38 2 (:DEFINITION FTY::RESERRP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (10 4 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 2 (:DEFINITION ALISTP))
 (3 1 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(YUL::RENAMING-RESULT-FIX-WHEN-ERR
 (22 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (19 1 (:DEFINITION FTY::RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 1 (:DEFINITION ALISTP))
 (3 1 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION STRIP-CARS))
 )
(YUL::EQUAL-OF-RENAMING-RESULT-ERR
 (114 6 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (96 6 (:DEFINITION FTY::RESERRP))
 (30 23 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (24 6 (:DEFINITION ALISTP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (20 20 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (12 6 (:DEFINITION STRIP-CARS))
 (10 2 (:REWRITE FTY::RESERRP-WHEN-RESERR-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERR-OPTIONP))
 (4 4 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (4 2 (:REWRITE FTY::RESERR-OPTIONP-WHEN-RESERRP))
 )
(YUL::RENAMING-RESULT-ERR-OF-RESERR-FIX-GET)
(YUL::RENAMING-RESULT-ERR-RESERR-EQUIV-CONGRUENCE-ON-GET)
(YUL::RENAMING-RESULT-FIX-REDEF
 (9 3 (:REWRITE YUL::RENAMING-RESULT-FIX-WHEN-RENAMING-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION YUL::RENAMING-RESULTP))
 )
(YUL::RENAMING-RESULTP-WHEN-RENAMINGP)
(YUL::RENAMING-RESULTP-WHEN-RESERRP)
(YUL::NOT-RESERRP-WHEN-RENAMINGP
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(YUL::RENAMINGP-WHEN-RENAMING-RESULTP-AND-NOT-RESERRP)
(YUL::LEMMA-LEMMA
 (490 6 (:REWRITE MEMBER-EQUAL-OF-STRIP-CARS-WHEN-MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (320 6 (:REWRITE MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (282 6 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (65 33 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (57 57 (:REWRITE SUBSETP-MEMBER . 2))
 (57 57 (:REWRITE DEFAULT-CDR))
 (51 45 (:REWRITE SUBSETP-MEMBER . 3))
 (45 45 (:REWRITE SUBSETP-MEMBER . 4))
 (45 45 (:REWRITE INTERSECTP-MEMBER . 3))
 (45 45 (:REWRITE INTERSECTP-MEMBER . 2))
 (37 37 (:REWRITE SUBSETP-TRANS2))
 (37 37 (:REWRITE SUBSETP-TRANS))
 (36 36 (:TYPE-PRESCRIPTION HONS-DUPLICATED-MEMBERS-AUX))
 (33 33 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (30 30 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 )
(YUL::LEMMA
 (599 11 (:REWRITE MEMBER-EQUAL-OF-STRIP-CARS-WHEN-MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (265 11 (:REWRITE MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (259 250 (:REWRITE DEFAULT-CAR))
 (236 188 (:REWRITE SUBSETP-MEMBER . 1))
 (215 149 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (188 188 (:REWRITE SUBSETP-MEMBER . 2))
 (173 173 (:REWRITE SUBSETP-TRANS2))
 (173 173 (:REWRITE SUBSETP-TRANS))
 (152 134 (:REWRITE SUBSETP-MEMBER . 3))
 (149 149 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (134 134 (:REWRITE SUBSETP-MEMBER . 4))
 (134 134 (:REWRITE INTERSECTP-MEMBER . 3))
 (134 134 (:REWRITE INTERSECTP-MEMBER . 2))
 (69 69 (:TYPE-PRESCRIPTION HONS-DUPLICATED-MEMBERS-AUX))
 (18 18 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (16 2 (:DEFINITION HONS-ASSOC-EQUAL))
 (10 2 (:DEFINITION NFIX))
 (6 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:DEFINITION HONS-EQUAL))
 )
(YUL::RENAMING-PAIR-EQUALITY)
(YUL::RENAMING-OLD)
(YUL::IDENTIFIER-SETP-OF-RENAMING-OLD
 (19 1 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (6 1 (:DEFINITION STRIP-CARS))
 (4 1 (:REWRITE YUL::IDENTIFIER-LISTP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (3 1 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (3 1 (:REWRITE YUL::SETP-WHEN-IDENTIFIER-SETP))
 (3 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING->LIST$INLINE))
 (2 2 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE YUL::IDENTIFIER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(YUL::OLD-VAR-IN-RENAMING-OLD-WHEN-IN-RENAMING
 (1307 26 (:REWRITE MEMBER-EQUAL-OF-STRIP-CARS-WHEN-MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (1036 26 (:REWRITE MEMBER-EQUAL-OF-HONS-DUPLICATED-MEMBERS-AUX))
 (484 117 (:REWRITE SUBSETP-MEMBER . 3))
 (376 8 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (257 257 (:REWRITE DEFAULT-CAR))
 (252 198 (:REWRITE DEFAULT-CDR))
 (219 87 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (192 87 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (192 16 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (180 18 (:DEFINITION HONS-ASSOC-EQUAL))
 (162 162 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (151 151 (:REWRITE SUBSETP-MEMBER . 2))
 (130 13 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (117 117 (:REWRITE SUBSETP-MEMBER . 4))
 (117 117 (:REWRITE INTERSECTP-MEMBER . 3))
 (117 117 (:REWRITE INTERSECTP-MEMBER . 2))
 (90 18 (:DEFINITION NFIX))
 (89 89 (:REWRITE SUBSETP-TRANS2))
 (89 89 (:REWRITE SUBSETP-TRANS))
 (58 58 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (54 36 (:REWRITE DEFAULT-<-2))
 (50 50 (:TYPE-PRESCRIPTION HONS-DUPLICATED-MEMBERS-AUX))
 (36 36 (:REWRITE DEFAULT-<-1))
 (32 32 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (32 16 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (32 16 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (32 16 (:REWRITE YUL::SETP-WHEN-IDENTIFIER-SETP))
 (32 16 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 18 (:REWRITE YUL::RENAMING-REQUIREMENTS))
 (18 18 (:DEFINITION HONS-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (16 16 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (16 16 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SETP))
 (16 16 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (16 16 (:REWRITE SET::IN-SET))
 )
(YUL::RENAMING-OLD-OF-RENAMING-FIX-REN)
(YUL::RENAMING-OLD-RENAMING-EQUIV-CONGRUENCE-ON-REN)
(YUL::RENAMING-NEW)
(YUL::IDENTIFIER-SETP-OF-RENAMING-NEW
 (19 1 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (6 1 (:DEFINITION STRIP-CDRS))
 (4 1 (:REWRITE YUL::IDENTIFIER-LISTP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (3 1 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (3 1 (:REWRITE YUL::SETP-WHEN-IDENTIFIER-SETP))
 (3 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION YUL::RENAMING->LIST$INLINE))
 (2 2 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE YUL::IDENTIFIER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(YUL::NEW-VAR-IN-RENAMING-NEW-WHEN-IN-RENAMING
 (468 101 (:REWRITE SUBSETP-MEMBER . 3))
 (192 16 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (178 64 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (166 64 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (130 13 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (117 117 (:REWRITE DEFAULT-CDR))
 (101 101 (:REWRITE SUBSETP-MEMBER . 4))
 (101 101 (:REWRITE SUBSETP-MEMBER . 2))
 (101 101 (:REWRITE INTERSECTP-MEMBER . 3))
 (101 101 (:REWRITE INTERSECTP-MEMBER . 2))
 (84 84 (:REWRITE DEFAULT-CAR))
 (66 66 (:REWRITE SUBSETP-TRANS2))
 (66 66 (:REWRITE SUBSETP-TRANS))
 (32 32 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (32 16 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (32 16 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (32 16 (:REWRITE YUL::SETP-WHEN-IDENTIFIER-SETP))
 (32 16 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (16 16 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (16 16 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (16 16 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SETP))
 (16 16 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (16 16 (:REWRITE SET::IN-SET))
 )
(YUL::RENAMING-NEW-OF-RENAMING-FIX-REN)
(YUL::RENAMING-NEW-RENAMING-EQUIV-CONGRUENCE-ON-REN)
