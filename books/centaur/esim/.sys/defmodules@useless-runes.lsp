(VL2014::VL-SIMPLIFY-MAYBE-CLEAN-PARAMS)
(VL2014::VL-DESIGN-P-OF-VL-SIMPLIFY-MAYBE-CLEAN-PARAMS)
(VL2014::VL-SIMPLIFY-MAIN
 (76 4 (:REWRITE VL2014::VL-DESIGN-P-BY-TAG-WHEN-VL-SCOPE-P))
 (63 1 (:REWRITE LEN-WHEN-ATOM))
 (6 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (5 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-USELESS-PARAMS-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TRANSLATION-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TIMETOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TF-PARSED-VAR-ID-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-SYSIDTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-STRINGTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-REALTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-PSCONFIG-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-PARSED-ANSI-PORT-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-INTTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-IFRAME-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-IDTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-EXTINTTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-ERANGE-P))
 (4 2 (:REWRITE VL2014::EQUAL-WHEN-VL-EMODWIRE-P))
 (4 2 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (4 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P . 1))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-USELESS-PARAMS-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TRANSLATION-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TIMETOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TF-PARSED-VAR-ID-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-SYSIDTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-STRINGTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-REALTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PSCONFIG-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PARSED-ANSI-PORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-INTTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IFRAME-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IDTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EXTINTTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-ERANGE-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EMODWIRE-P))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-EMPTY-LEXSCOPE$INLINE))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE VL2014::VL-LEXSCOPE-P-OF-VL-EMPTY-LEXSCOPE))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSET))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USERTYPES-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USERTYPES-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USELESS-PARAMS-MAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USELESS-PARAMS-MAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-SIGALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-SIGALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-EXPR-PAIRS-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-EXPR-PAIRS-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SIGMA-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SIGMA-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RES-SIGMA-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RES-SIGMA-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PRIMALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PRIMALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODITEM-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODITEM-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EXPR-VAL-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EXPR-VAL-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EDGETABLE-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EDGETABLE-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(VL2014::VL-DESIGN-P-OF-VL-SIMPLIFY-MAIN.GOOD
 (46 1 (:REWRITE VL2014::VL-DESIGN-FIX-WHEN-VL-DESIGN-P))
 (37 1 (:REWRITE VL2014::VL-DESIGN-P-BY-TAG-WHEN-VL-SCOPE-P))
 (5 1 (:REWRITE VL2014::VL-DESIGN-P-WHEN-VL-MAYBE-DESIGN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MAYBE-DESIGN-P))
 (2 2 (:META VL2014::VL-DESIGN-P-OF-HIDE-META-CORRECT))
 (2 1 (:REWRITE VL2014::VL-MAYBE-DESIGN-P-WHEN-VL-DESIGN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-USELESS-PARAMS-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TRANSLATION-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TIMETOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TF-PARSED-VAR-ID-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-SYSIDTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-STRINGTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-REALTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-PSCONFIG-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-PARSED-ANSI-PORT-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-INTTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-IFRAME-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-IDTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-EXTINTTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-ERANGE-P))
 (2 1 (:REWRITE VL2014::EQUAL-WHEN-VL-EMODWIRE-P))
 (2 1 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (1 1 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-USELESS-PARAMS-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TRANSLATION-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TIMETOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TF-PARSED-VAR-ID-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-SYSIDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-STRINGTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-REALTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PSCONFIG-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PARSED-ANSI-PORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-INTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IFRAME-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EXTINTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-ERANGE-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EMODWIRE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-WARNINGLIST-FIX-UNDER-VL-WARNINGLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-VARDECLLIST-FIX-UNDER-VL-VARDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-UDPLIST-FIX-UNDER-VL-UDPLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-TYPEDEFLIST-FIX-UNDER-VL-TYPEDEFLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-TASKDECLLIST-FIX-UNDER-VL-TASKDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-SYNTAXVERSION-FIX-UNDER-VL-SYNTAXVERSION-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PROGRAMLIST-FIX-UNDER-VL-PROGRAMLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PARAMDECLLIST-FIX-UNDER-VL-PARAMDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PACKAGELIST-FIX-UNDER-VL-PACKAGELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-MODULELIST-FIX-UNDER-VL-MODULELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-INTERFACELIST-FIX-UNDER-VL-INTERFACELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-IMPORTLIST-FIX-UNDER-VL-IMPORTLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-FWDTYPEDEFLIST-FIX-UNDER-VL-FWDTYPEDEFLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-FUNDECLLIST-FIX-UNDER-VL-FUNDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-CONFIGLIST-FIX-UNDER-VL-CONFIGLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-COMMENTMAP-FIX-UNDER-VL-COMMENTMAP-EQUIV))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(VL2014::VL-DESIGN-P-OF-VL-SIMPLIFY-MAIN.BAD
 (46 1 (:REWRITE VL2014::VL-DESIGN-FIX-WHEN-VL-DESIGN-P))
 (37 1 (:REWRITE VL2014::VL-DESIGN-P-BY-TAG-WHEN-VL-SCOPE-P))
 (5 1 (:REWRITE VL2014::VL-DESIGN-P-WHEN-VL-MAYBE-DESIGN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-MAYBE-DESIGN-P))
 (2 2 (:META VL2014::VL-DESIGN-P-OF-HIDE-META-CORRECT))
 (2 1 (:REWRITE VL2014::VL-MAYBE-DESIGN-P-WHEN-VL-DESIGN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-USELESS-PARAMS-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TRANSLATION-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TIMETOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-TF-PARSED-VAR-ID-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-SYSIDTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-STRINGTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-REALTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-PSCONFIG-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-PARSED-ANSI-PORT-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-INTTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-IFRAME-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-IDTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-EXTINTTOKEN-P))
 (2 1 (:REWRITE VL2014::TAG-WHEN-VL-ERANGE-P))
 (2 1 (:REWRITE VL2014::EQUAL-WHEN-VL-EMODWIRE-P))
 (2 1 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (1 1 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-USELESS-PARAMS-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TRANSLATION-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TIMETOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TF-PARSED-VAR-ID-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-SYSIDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-STRINGTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-REALTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PSCONFIG-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PARSED-ANSI-PORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-INTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IFRAME-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EXTINTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-ERANGE-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EMODWIRE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-WARNINGLIST-FIX-UNDER-VL-WARNINGLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-VARDECLLIST-FIX-UNDER-VL-VARDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-UDPLIST-FIX-UNDER-VL-UDPLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-TYPEDEFLIST-FIX-UNDER-VL-TYPEDEFLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-TASKDECLLIST-FIX-UNDER-VL-TASKDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-SYNTAXVERSION-FIX-UNDER-VL-SYNTAXVERSION-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PROGRAMLIST-FIX-UNDER-VL-PROGRAMLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PARAMDECLLIST-FIX-UNDER-VL-PARAMDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PACKAGELIST-FIX-UNDER-VL-PACKAGELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-MODULELIST-FIX-UNDER-VL-MODULELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-INTERFACELIST-FIX-UNDER-VL-INTERFACELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-IMPORTLIST-FIX-UNDER-VL-IMPORTLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-FWDTYPEDEFLIST-FIX-UNDER-VL-FWDTYPEDEFLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-FUNDECLLIST-FIX-UNDER-VL-FUNDECLLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-CONFIGLIST-FIX-UNDER-VL-CONFIGLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL2014::VL-COMMENTMAP-FIX-UNDER-VL-COMMENTMAP-EQUIV))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(VL2014::VL-SIMPLIFY
 (75 3 (:REWRITE VL2014::VL-DESIGN-P-BY-TAG-WHEN-VL-SCOPE-P))
 (4 4 (:META VL2014::VL-DESIGN-P-OF-HIDE-META-CORRECT))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-USELESS-PARAMS-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TRANSLATION-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TIMETOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-TF-PARSED-VAR-ID-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-SYSIDTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-STRINGTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-REALTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-PSCONFIG-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-PARSED-ANSI-PORT-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-OPINFO-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-INTTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-IFRAME-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-IDTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-EXTINTTOKEN-P))
 (4 2 (:REWRITE VL2014::TAG-WHEN-VL-ERANGE-P))
 (4 2 (:REWRITE VL2014::EQUAL-WHEN-VL-EMODWIRE-P))
 (4 2 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-USELESS-PARAMS-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TRANSLATION-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TIMETOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TF-PARSED-VAR-ID-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-SYSIDTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-STRINGTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-REALTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PSCONFIG-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PARSED-ANSI-PORT-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-OPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-INTTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IFRAME-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IDTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EXTINTTOKEN-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-ERANGE-P))
 (2 2 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EMODWIRE-P))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(VL2014::VL-DESIGN-P-OF-VL-SIMPLIFY.GOOD)
(VL2014::VL-DESIGN-P-OF-VL-SIMPLIFY.BAD)
(VL2014::DEFMODULES-FN-FN
 (245 3 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (192 6 (:REWRITE LEN-WHEN-ATOM))
 (126 2 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (38 2 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (36 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P . 1))
 (30 10 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (30 2 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (24 2 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (18 18 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (18 18 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (18 9 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (9 9 (:TYPE-PRESCRIPTION VL2014::VL-EMPTY-LEXSCOPE$INLINE))
 (9 9 (:REWRITE VL2014::VL-LEXSCOPE-P-OF-VL-EMPTY-LEXSCOPE))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USERTYPES-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USERTYPES-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USELESS-PARAMS-MAP-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-USELESS-PARAMS-MAP-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-SIGALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-SIGALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-EXPR-PAIRS-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-EXPR-PAIRS-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SIGMA-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SIGMA-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RES-SIGMA-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RES-SIGMA-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PRIMALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PRIMALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODITEM-ALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODITEM-ALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EXPR-VAL-ALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EXPR-VAL-ALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EDGETABLE-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EDGETABLE-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-EALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 1))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (9 9 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (9 9 (:REWRITE CONSP-BY-LEN))
 (8 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (8 2 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (6 6 (:REWRITE-QUOTED-CONSTANT VL2014::VL-PRINTABLE-FIX-UNDER-VL-PRINTABLE-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT VL2014::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT MAYBE-NATP-FIX-UNDER-MAYBE-NAT-EQUIV))
 (6 6 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (6 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION STRING-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (4 4 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (4 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-VL-EMODWIRELIST-P))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (3 3 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE VL2014::VL-MODULELIST->NAMES-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION VL2014::VL-EMODWIRELIST-P))
 (2 2 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSET))
 (2 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (2 2 (:META VL2014::VL-DESIGN-P-OF-HIDE-META-CORRECT))
 )
(VL2014::VL-TRANSLATION-P-OF-DEFMODULES-FN.TRANS
 (58 1 (:REWRITE VL2014::VL-TRANSLATION-P-WHEN-WRONG-TAG))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-USELESS-PARAMS-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-TRANSLATION-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-TIMETOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-TF-PARSED-VAR-ID-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-SYSIDTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-STRINGTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-REALTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-PSCONFIG-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-PARSED-ANSI-PORT-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-INTTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-IFRAME-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-IDTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-EXTINTTOKEN-P))
 (4 1 (:REWRITE VL2014::TAG-WHEN-VL-ERANGE-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-USELESS-PARAMS-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TIMETOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-TF-PARSED-VAR-ID-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-SYSIDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-STRINGTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-REALTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PSCONFIG-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-PARSED-ANSI-PORT-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-INTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IFRAME-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-IDTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-EXTINTTOKEN-P))
 (1 1 (:TYPE-PRESCRIPTION VL2014::BOOLEANP-OF-VL-ERANGE-P))
 (1 1 (:REWRITE VL2014::TAG-OF-VL-TRANSLATION))
 (1 1 (:META VL2014::VL-DESIGN-P-OF-HIDE-META-CORRECT))
 )
(VL2014::STATE-P1-OF-DEFMODULES-FN.STATE
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 )
