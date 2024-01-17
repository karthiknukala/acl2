(ZCASH::VERIFY-GUARDS-LEMMA
 (173 19 (:REWRITE BYTE-LISTP-OF-CDR-WHEN-BYTE-LISTP))
 (122 88 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (50 4 (:DEFINITION MEMBER-EQUAL))
 (27 27 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (14 2 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (14 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (13 13 (:REWRITE SUBSETP-TRANS2))
 (13 13 (:REWRITE SUBSETP-TRANS))
 (13 10 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (2 2 (:REWRITE MEMBER-OF-CAR))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ZCASH::RETURNS-LEMMA
 (55 15 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
 (50 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (35 8 (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
 (32 2 (:DEFINITION MEMBER-EQUAL))
 (26 20 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (19 17 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (18 18 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (15 15 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (14 2 (:REWRITE BYTE-LISTP-OF-CDR-WHEN-BYTE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 2 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (10 10 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
 (10 10 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (9 9 (:REWRITE SUBSETP-TRANS2))
 (9 9 (:REWRITE SUBSETP-TRANS))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (6 6 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(ZCASH::BLAKE2S-256
 (16 4 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (15 3 (:DEFINITION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 2 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(ZCASH::BYTE-LISTP-OF-BLAKE2S-256)
(ZCASH::LEN-OF-BLAKE2S-256)
