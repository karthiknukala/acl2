(JAVA::ATJ-CHAR-TO-JCHARS-ID
 (44 14 (:REWRITE DEFAULT-CDR))
 (30 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (16 16 (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
 (16 16 (:REWRITE DEFAULT-CHAR-CODE))
 (8 8 (:REWRITE STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP))
 (8 8 (:REWRITE STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(JAVA::CHARACTER-LISTP-OF-ATJ-CHAR-TO-JCHARS-ID
 (114 15 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (51 13 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CONS))
 (42 42 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (35 21 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (30 6 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (29 15 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (25 19 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION UBYTE8=>HEXCHARS))
 (24 24 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (16 16 (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LISTP))
 (16 8 (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
 (16 8 (:REWRITE STR::DEC-DIGIT-CHAR-P-WHEN-NONZERO-DEC-DIGIT-CHAR-P))
 (15 15 (:REWRITE DEFAULT-CHAR-CODE))
 (12 12 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-P$INLINE))
 (12 12 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-P$INLINE))
 (12 12 (:REWRITE STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP))
 (12 12 (:REWRITE STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP))
 (11 11 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
 (8 8 (:TYPE-PRESCRIPTION STR::NONZERO-DEC-DIGIT-CHAR-P$INLINE))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (8 6 (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
 (2 2 (:REWRITE STR::UPCASE-CHAR-DOES-NOTHING-UNLESS-DOWN-ALPHA-P))
 (2 2 (:REWRITE STR::DOWNCASE-CHAR-DOES-NOTHING-UNLESS-UP-ALPHA-P))
 (2 1 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(JAVA::ATJ-CHARS-TO-JCHARS-ID
 (90 12 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (66 12 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (24 24 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (18 9 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP))
 (18 9 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (12 12 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (12 12 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(JAVA::CHARACTER-LISTP-OF-ATJ-CHARS-TO-JCHARS-ID
 (222 39 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (85 84 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (54 40 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (48 24 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP))
 (48 24 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (26 26 (:REWRITE DEFAULT-CDR))
 (25 25 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (25 25 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (18 1 (:DEFINITION BINARY-APPEND))
 (17 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-APPEND))
 (8 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-APPEND))
 (6 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1 1 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE SET::IN-SET))
 )
(JAVA::ATJ-VAR-TO-JVAR
 (273 82 (:REWRITE DEFAULT-CAR))
 (186 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (136 8 (:DEFINITION TRUE-LISTP))
 (124 45 (:REWRITE DEFAULT-CDR))
 (97 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (97 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (97 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (97 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (97 97 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (91 16 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (89 89 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (66 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (60 3 (:DEFINITION BINARY-APPEND))
 (45 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (36 3 (:DEFINITION REMOVE-EQUAL))
 (31 31 (:REWRITE DEFAULT-SYMBOL-NAME))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (28 1 (:DEFINITION ALISTP))
 (22 2 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (21 20 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (18 9 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (18 9 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (17 17 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (16 2 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (15 15 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (15 15 (:REWRITE SET::IN-SET))
 (13 1 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-APPEND))
 (10 7 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (8 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-APPEND))
 (4 4 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (4 4 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CONS))
 (4 4 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CONS))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 )
(JAVA::SYMBOLP-OF-ATJ-VAR-TO-JVAR)
(JAVA::ATJ-VAR-ADD-INDEX
 (38 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (23 5 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (11 11 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LISTP))
 (10 10 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (8 5 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (6 4 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (4 3 (:REWRITE DEFAULT-CDR))
 (4 3 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (1 1 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CONS))
 (1 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CONS))
 )
(JAVA::SYMBOLP-OF-ATJ-VAR-ADD-INDEX)
(JAVA::ATJ-PKG-TO-CLASS)
(JAVA::STRINGP-OF-ATJ-PKG-TO-CLASS)
(JAVA::ATJ-PKGS-TO-CLASSES
 (564 38 (:REWRITE SUBSETP-CAR-MEMBER))
 (276 48 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (181 16 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (162 162 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (130 10 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (128 15 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (91 89 (:REWRITE DEFAULT-CDR))
 (75 74 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (48 48 (:REWRITE SUBSETP-TRANS2))
 (48 48 (:REWRITE SUBSETP-TRANS))
 (47 47 (:REWRITE SUBSETP-MEMBER . 4))
 (47 47 (:REWRITE SUBSETP-MEMBER . 3))
 (47 47 (:REWRITE SUBSETP-MEMBER . 2))
 (47 47 (:REWRITE INTERSECTP-MEMBER . 3))
 (47 47 (:REWRITE INTERSECTP-MEMBER . 2))
 (31 31 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (30 30 (:REWRITE STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP))
 (30 30 (:REWRITE STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP))
 (6 1 (:REWRITE HONS-DUPLICITY-ALIST-P-OF-CONS))
 )
(JAVA::STRING-STRING-ALISTP-OF-ATJ-PKGS-TO-CLASSES
 (211 22 (:REWRITE STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP))
 (153 9 (:DEFINITION MEMBER-EQUAL))
 (123 12 (:REWRITE STRING-STRING-ALISTP-WHEN-NOT-CONSP))
 (71 71 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (63 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (37 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (37 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (37 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (37 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (37 37 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (33 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (30 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (24 23 (:REWRITE DEFAULT-CDR))
 (23 22 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP))
 (18 18 (:REWRITE SUBSETP-MEMBER . 2))
 (18 18 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 )
(JAVA::ATJ-GET-PKG-CLASS-NAME)
(JAVA::STRINGP-OF-ATJ-GET-PKG-CLASS-NAME
 (40 12 (:REWRITE DEFAULT-CAR))
 (22 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (14 2 (:REWRITE STRING-STRING-ALISTP-WHEN-NOT-CONSP))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE STRING-STRING-ALISTP-WHEN-SUBSETP-EQUAL))
 )
(JAVA::ATJ-FN-TO-METHOD
 (63 63 (:REWRITE SUBSETP-MEMBER . 4))
 (63 63 (:REWRITE SUBSETP-MEMBER . 3))
 (63 63 (:REWRITE SUBSETP-MEMBER . 2))
 (63 63 (:REWRITE SUBSETP-MEMBER . 1))
 (63 63 (:REWRITE INTERSECTP-MEMBER . 3))
 (63 63 (:REWRITE INTERSECTP-MEMBER . 2))
 (7 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (5 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (2 2 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 1 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 )
(JAVA::STRINGP-OF-ATJ-FN-TO-METHOD
 (63 63 (:REWRITE SUBSETP-MEMBER . 4))
 (63 63 (:REWRITE SUBSETP-MEMBER . 3))
 (63 63 (:REWRITE SUBSETP-MEMBER . 2))
 (63 63 (:REWRITE SUBSETP-MEMBER . 1))
 (63 63 (:REWRITE INTERSECTP-MEMBER . 3))
 (63 63 (:REWRITE INTERSECTP-MEMBER . 2))
 (30 2 (:DEFINITION BINARY-APPEND))
 (25 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (4 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(JAVA::ATJ-FNS-TO-METHODS
 (446 30 (:REWRITE SUBSETP-CAR-MEMBER))
 (218 38 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (183 16 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (159 159 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (129 16 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (104 8 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (88 87 (:REWRITE DEFAULT-CDR))
 (77 76 (:REWRITE DEFAULT-CAR))
 (56 56 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP))
 (52 52 (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP))
 (39 39 (:REWRITE SUBSETP-MEMBER . 4))
 (39 39 (:REWRITE SUBSETP-MEMBER . 3))
 (39 39 (:REWRITE SUBSETP-MEMBER . 2))
 (39 39 (:REWRITE INTERSECTP-MEMBER . 3))
 (39 39 (:REWRITE INTERSECTP-MEMBER . 2))
 (38 38 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (38 38 (:REWRITE SUBSETP-TRANS2))
 (38 38 (:REWRITE SUBSETP-TRANS))
 (32 32 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (16 1 (:REWRITE HONS-DUPLICITY-ALIST-P-OF-CONS))
 (3 1 (:DEFINITION NATP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(JAVA::SYMBOL-STRING-ALISTP-OF-ATJ-FNS-TO-METHODS
 (294 42 (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP))
 (204 12 (:DEFINITION MEMBER-EQUAL))
 (107 107 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (105 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (83 8 (:REWRITE SYMBOL-STRING-ALISTP-WHEN-NOT-CONSP))
 (80 80 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (45 45 (:REWRITE DEFAULT-CDR))
 (35 35 (:REWRITE DEFAULT-CAR))
 (33 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (30 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (24 24 (:REWRITE SUBSETP-MEMBER . 2))
 (24 24 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 )
(JAVA::ATJ-GET-FN-METHOD-NAME)
(JAVA::STRINGP-OF-ATJ-GET-FN-METHOD-NAME
 (40 12 (:REWRITE DEFAULT-CAR))
 (24 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 1))
 (14 2 (:REWRITE SYMBOL-STRING-ALISTP-WHEN-NOT-CONSP))
 (13 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-STRING-ALISTP . 2))
 (13 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (13 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (13 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 2))
 (13 13 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP . 1))
 (13 1 (:REWRITE STRINGP-OF-CDR-OF-ASSOC-EQUAL-WHEN-STRING-STRING-ALISTP))
 (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 1 (:REWRITE STRING-STRING-ALISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE SYMBOL-STRING-ALISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-STRING-STRING-ALISTP))
 (2 2 (:REWRITE STRING-STRING-ALISTP-WHEN-SUBSETP-EQUAL))
 )
