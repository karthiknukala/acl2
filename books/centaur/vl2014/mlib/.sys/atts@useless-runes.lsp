(VL2014::VL-GATHER-PORTDECLS-WITH-ATTRIBUTE
 (70 7 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (68 1 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (47 20 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (40 40 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (40 40 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 1 (:REWRITE VL2014::VL-PORTDECLLIST-P-WHEN-NOT-CONSP))
 (16 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (14 2 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (14 2 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (14 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (13 13 (:REWRITE CONSP-BY-LEN))
 (13 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (12 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (8 4 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (8 4 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (8 2 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 1 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (2 2 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (1 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::VL-PORTDECLLIST-P-OF-VL-GATHER-PORTDECLS-WITH-ATTRIBUTE
 (142 2 (:REWRITE STR-FIX-DEFAULT))
 (136 2 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (68 2 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (64 2 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (57 1 (:REWRITE VL2014::VL-PORTDECL-FIX-WHEN-VL-PORTDECL-P))
 (40 4 (:REWRITE VL2014::VL-PORTDECL-P-WHEN-MEMBER-EQUAL-OF-VL-PORTDECLLIST-P))
 (34 13 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (32 2 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (32 1 (:REWRITE SUBSETP-OF-CONS))
 (28 2 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (26 2 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (24 2 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (20 8 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (20 4 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (20 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (16 16 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (16 16 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (16 1 (:REWRITE SUBSETP-CAR-MEMBER))
 (13 3 (:REWRITE VL2014::VL-PORTDECLLIST-P-WHEN-NOT-CONSP))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (12 1 (:REWRITE VL2014::VL-PORTDECL-P-OF-CAR-WHEN-VL-PORTDECLLIST-P))
 (11 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (8 2 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (4 4 (:TYPE-PRESCRIPTION VL2014::VL-PORTDECL-P))
 (4 4 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (4 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 4 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-VARDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-TYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-TASKDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-PORTDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-PARAMDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-MODPORT-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-MODINST-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-INITIAL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-IMPORT-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-GENVAR-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-GATEINST-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-FWDTYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-FUNDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ASSIGN-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ALWAYS-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ALIAS-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-VARDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-TYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-TASKDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-REGULARPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-PORTDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-PARAMDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-MODPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-MODINST-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-INTERFACEPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-INITIAL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-IMPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-GENELEMENT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-GATEINST-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-FWDTYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-FUNDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ASSIGN-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ALWAYS-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ALIAS-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-VARDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-TYPEDEF-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-TASKDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-PARAMDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODPORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODINST-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODELEMENT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-INITIAL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-IMPORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-GATEINST-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-FWDTYPEDEF-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-FUNDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-CTXELEMENT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ASSIGN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ALWAYS-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ALIAS-P))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-MEMBER-EQUAL-OF-VL-MODELEMENTLIST-P))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:REWRITE VL2014::TAG-OF-VL-PORTDECL-FIX))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (2 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-REGULARPORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-INTERFACEPORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-GENVAR-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-GENELEMENT-P))
 )
(VL2014::VL-GATHER-PORTDECLS-WITH-ATTRIBUTE-OF-VL-PORTDECLLIST-FIX-X
 (570 10 (:REWRITE STR-FIX-DEFAULT))
 (544 8 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (128 8 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (121 15 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (112 8 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (104 8 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (96 22 (:REWRITE DEFAULT-CDR))
 (96 8 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (82 37 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (82 10 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (53 53 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 8 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (44 44 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (42 21 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (40 40 (:REWRITE VL2014::VL-PORTDECLLIST-P-WHEN-SUBSETP-EQUAL))
 (36 6 (:REWRITE VL2014::VL-PORTDECLLIST-P-OF-CDR-WHEN-VL-PORTDECLLIST-P))
 (32 32 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (32 8 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (29 29 (:REWRITE CONSP-BY-LEN))
 (26 10 (:REWRITE STR-FIX-WHEN-STRINGP))
 (26 2 (:REWRITE VL2014::VL-PORTDECL-FIX-WHEN-VL-PORTDECL-P))
 (21 21 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (21 21 (:REWRITE SET::IN-SET))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (17 17 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (16 16 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (16 16 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (16 16 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (16 16 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (16 14 (:REWRITE DEFAULT-CAR))
 (16 8 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (8 8 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (8 8 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (8 8 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (8 8 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (8 8 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE FN-CHECK-DEF-FORMALS))
 (8 8 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (7 1 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (6 6 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 1 (:REWRITE VL2014::VL-PORTDECL-P-OF-CAR-WHEN-VL-PORTDECLLIST-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-PORTDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:REWRITE VL2014::VL-PORTDECL-P-WHEN-MEMBER-EQUAL-OF-VL-PORTDECLLIST-P))
 )
(VL2014::VL-GATHER-PORTDECLS-WITH-ATTRIBUTE-VL-PORTDECLLIST-EQUIV-CONGRUENCE-ON-X)
(VL2014::VL-GATHER-PORTDECLS-WITH-ATTRIBUTE-OF-STR-FIX-ATT
 (428 8 (:REWRITE STR-FIX-DEFAULT))
 (408 6 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (96 6 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (84 6 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (78 6 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (72 6 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (42 6 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (28 12 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 2 (:REWRITE VL2014::VL-PORTDECL-FIX-WHEN-VL-PORTDECL-P))
 (24 24 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (24 6 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (22 4 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 12 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (12 12 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (12 12 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (12 6 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8 (:REWRITE SET::IN-SET))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (8 8 (:REWRITE CONSP-BY-LEN))
 (8 8 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (7 1 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-PORTDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (6 6 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (6 6 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (6 6 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE VL2014::VL-PORTDECL-P-OF-CAR-WHEN-VL-PORTDECLLIST-P))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-PORTDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:REWRITE VL2014::VL-PORTDECLLIST-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::VL-PORTDECL-P-WHEN-MEMBER-EQUAL-OF-VL-PORTDECLLIST-P))
 (1 1 (:REWRITE VL2014::VL-PORTDECLLIST-P-WHEN-NOT-CONSP))
 )
(VL2014::VL-GATHER-PORTDECLS-WITH-ATTRIBUTE-STREQV-CONGRUENCE-ON-ATT)
(VL2014::VL-GATHER-VARDECLS-WITH-ATTRIBUTE
 (70 7 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (68 1 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (47 20 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (40 40 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (40 40 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 1 (:REWRITE VL2014::VL-VARDECLLIST-P-WHEN-NOT-CONSP))
 (16 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (14 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (14 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (14 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-BLOCKITEM-P))
 (14 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (13 13 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (13 13 (:REWRITE CONSP-BY-LEN))
 (13 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (12 6 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (12 6 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (12 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 2 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (6 6 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4 1 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (2 2 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (1 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::VL-VARDECLLIST-P-OF-VL-GATHER-VARDECLS-WITH-ATTRIBUTE
 (142 2 (:REWRITE STR-FIX-DEFAULT))
 (136 2 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (68 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (64 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (64 1 (:REWRITE VL2014::VL-VARDECL-FIX-WHEN-VL-VARDECL-P))
 (40 4 (:REWRITE VL2014::VL-VARDECL-P-WHEN-MEMBER-EQUAL-OF-VL-VARDECLLIST-P))
 (34 13 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (32 2 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (32 1 (:REWRITE SUBSETP-OF-CONS))
 (28 2 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (26 2 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (25 2 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-BLOCKITEM-P))
 (24 2 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (20 8 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (20 4 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (20 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (16 16 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (16 16 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (16 1 (:REWRITE SUBSETP-CAR-MEMBER))
 (13 3 (:REWRITE VL2014::VL-VARDECLLIST-P-WHEN-NOT-CONSP))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (12 1 (:REWRITE VL2014::VL-VARDECL-P-OF-CAR-WHEN-VL-VARDECLLIST-P))
 (11 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (8 2 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 3 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (6 3 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (6 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 (5 5 (:TYPE-PRESCRIPTION VL2014::VL-VARDECL-P))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (4 4 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (4 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (4 4 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 4 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (3 3 (:TYPE-PRESCRIPTION VL2014::VL-PARAMDECL-P))
 (3 3 (:TYPE-PRESCRIPTION VL2014::VL-IMPORT-P))
 (3 3 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (3 3 (:REWRITE VL2014::TAG-OF-VL-VARDECL-FIX))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-VARDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-TYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-TASKDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-PORTDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-PARAMDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-MODPORT-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-MODINST-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-INITIAL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-IMPORT-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-GENVAR-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-GATEINST-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-FWDTYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-FUNDECL-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ASSIGN-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ALWAYS-P))
 (3 1 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-VL-ALIAS-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-VARDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-TYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-TASKDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-REGULARPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-PORTDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-PARAMDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-MODPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-MODINST-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-INTERFACEPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-INITIAL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-IMPORT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-GENELEMENT-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-GATEINST-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-FWDTYPEDEF-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-FUNDECL-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ASSIGN-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ALWAYS-P))
 (3 1 (:REWRITE VL2014::VL-CTXELEMENT-P-WHEN-VL-ALIAS-P))
 (3 1 (:REWRITE VL2014::VL-BLOCKITEM-P-WHEN-VL-VARDECL-P))
 (3 1 (:REWRITE VL2014::VL-BLOCKITEM-P-WHEN-VL-PARAMDECL-P))
 (3 1 (:REWRITE VL2014::VL-BLOCKITEM-P-WHEN-VL-IMPORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-TYPEDEF-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-TASKDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-PORTDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODPORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODINST-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MODELEMENT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-INITIAL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-GATEINST-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-FWDTYPEDEF-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-FUNDECL-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-CTXELEMENT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-BLOCKITEM-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ASSIGN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ALWAYS-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-ALIAS-P))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (2 2 (:REWRITE VL2014::VL-MODELEMENT-P-WHEN-MEMBER-EQUAL-OF-VL-MODELEMENTLIST-P))
 (2 2 (:REWRITE VL2014::VL-BLOCKITEM-P-WHEN-MEMBER-EQUAL-OF-VL-BLOCKITEMLIST-P))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (2 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-REGULARPORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-INTERFACEPORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-GENVAR-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-GENELEMENT-P))
 )
(VL2014::VL-GATHER-VARDECLS-WITH-ATTRIBUTE-OF-VL-VARDECLLIST-FIX-X
 (570 10 (:REWRITE STR-FIX-DEFAULT))
 (544 8 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (128 8 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (123 16 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (112 8 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (104 8 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (96 22 (:REWRITE DEFAULT-CDR))
 (96 8 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (82 37 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (82 10 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (53 53 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 8 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (45 45 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (42 21 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (40 40 (:REWRITE VL2014::VL-VARDECLLIST-P-WHEN-SUBSETP-EQUAL))
 (36 6 (:REWRITE VL2014::VL-VARDECLLIST-P-OF-CDR-WHEN-VL-VARDECLLIST-P))
 (33 2 (:REWRITE VL2014::VL-VARDECL-FIX-WHEN-VL-VARDECL-P))
 (32 32 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (32 8 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (29 29 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (29 29 (:REWRITE CONSP-BY-LEN))
 (26 10 (:REWRITE STR-FIX-WHEN-STRINGP))
 (21 21 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (21 21 (:REWRITE SET::IN-SET))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (21 21 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (17 17 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (16 16 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (16 16 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (16 16 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (16 16 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (16 14 (:REWRITE DEFAULT-CAR))
 (16 8 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (16 8 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (8 8 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (8 8 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (8 8 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (8 8 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (8 8 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (8 8 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE FN-CHECK-DEF-FORMALS))
 (8 8 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-BLOCKITEM-P))
 (6 6 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 3 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (6 1 (:REWRITE VL2014::VL-VARDECL-P-OF-CAR-WHEN-VL-VARDECLLIST-P))
 (3 3 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-VARDECL-P))
 (2 2 (:REWRITE VL2014::VL-VARDECL-P-WHEN-MEMBER-EQUAL-OF-VL-VARDECLLIST-P))
 )
(VL2014::VL-GATHER-VARDECLS-WITH-ATTRIBUTE-VL-VARDECLLIST-EQUIV-CONGRUENCE-ON-X)
(VL2014::VL-GATHER-VARDECLS-WITH-ATTRIBUTE-OF-STR-FIX-ATT
 (428 8 (:REWRITE STR-FIX-DEFAULT))
 (408 6 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (96 6 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (84 6 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (78 6 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (72 6 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (42 6 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (33 2 (:REWRITE VL2014::VL-VARDECL-FIX-WHEN-VL-VARDECL-P))
 (28 12 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (24 6 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (24 5 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (19 19 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 12 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (12 12 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (12 12 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (12 6 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8 (:REWRITE SET::IN-SET))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (8 8 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (8 8 (:REWRITE CONSP-BY-LEN))
 (8 8 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-MODELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-CTXELEMENT-P))
 (7 1 (:REWRITE VL2014::VL-VARDECL-P-BY-TAG-WHEN-VL-BLOCKITEM-P))
 (6 6 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (6 6 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (6 6 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (6 3 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (6 1 (:REWRITE VL2014::VL-VARDECL-P-OF-CAR-WHEN-VL-VARDECLLIST-P))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-VARDECL-P))
 (2 2 (:REWRITE VL2014::VL-VARDECLLIST-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::VL-VARDECL-P-WHEN-MEMBER-EQUAL-OF-VL-VARDECLLIST-P))
 (1 1 (:REWRITE VL2014::VL-VARDECLLIST-P-WHEN-NOT-CONSP))
 )
(VL2014::VL-GATHER-VARDECLS-WITH-ATTRIBUTE-STREQV-CONGRUENCE-ON-ATT)
