(VL::VL-TOOLKIT-HELP-MESSAGE)
(VL::VL-TOOLKIT-HELP-MESSAGE-CONSTRAINT)
(VL::VL-TOOLKIT-HELP-MESSAGE-DEFAULT)
(VL::RETURN-TYPE-OF-VL-TOOLKIT-HELP-MESSAGE-DEFAULT
 (115 1 (:REWRITE DEFAULT-CDR))
 (42 7 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (14 14 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (14 7 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 8 (:REWRITE VL::HONS-ASSOC-EQUAL-WHEN-VL-PREFIX-MAP-CORRECT-P-AUX))
 (8 8 (:REWRITE VL::HONS-ASSOC-EQUAL-WHEN-VL-PREFIX-MAP-CORRECT-P))
 (7 7 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (7 7 (:REWRITE SET::IN-SET))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 1))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (2 2 (:REWRITE VL::STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P))
 (2 2 (:REWRITE VL::STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P))
 (2 2 (:REWRITE VL::STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P))
 (2 2 (:REWRITE VL::STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P))
 (2 2 (:REWRITE VL::STRINGP-OF-CDR-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (2 1 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION VL::VL-ELABSCOPES-INIT))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
 (1 1 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 1))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 2))
 (1 1 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(VL::VL-HELP-FN
 (286 3 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (251 1 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (231 3 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (230 2 (:REWRITE MEMBER-WHEN-ATOM))
 (136 3 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (44 3 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (41 1 (:DEFINITION TRUE-LIST-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 4 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (21 3 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (21 3 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (20 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 1))
 (18 6 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (18 3 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (13 5 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (13 3 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (13 3 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (10 4 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (9 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (7 6 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (6 6 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (6 6 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (6 1 (:REWRITE VL::CONSP-OF-CAR-WHEN-VL-COMMENTMAP-P))
 (5 5 (:TYPE-PRESCRIPTION VL::VL-ELABSCOPES-INIT))
 (5 5 (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
 (5 5 (:REWRITE SET::IN-SET))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (5 5 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (4 4 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (4 3 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 1 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (3 3 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (3 3 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 1 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:REWRITE VL::VL-PRINTABLE-P-WHEN-CHARACTERP))
 (2 2 (:REWRITE VL::VL-PRINTABLE-P-WHEN-CHARACTER-LISTP))
 (2 2 (:REWRITE VL::VL-PRINTABLE-P-WHEN-ACL2-NUMBERP))
 (2 2 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (2 2 (:REWRITE SUBSETP-MEMBER . 4))
 (2 2 (:REWRITE SUBSETP-MEMBER . 3))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 3))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL::CHARACTER-LISTP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LIST-LISTP))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (2 1 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (2 1 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE VL::CHARACTER-LISTP-OF-CAR-WHEN-CHARACTER-LIST-LISTP))
 (1 1 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 (1 1 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 )
(VL::VL-TOOLKIT-OTHER-COMMAND)
(VL::VL-TOOLKIT-OTHER-COMMAND-DEFAULT)
(VL::VL-MAIN-FN
 (692 116 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (514 2 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (272 4 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (200 200 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (200 100 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (116 116 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (116 116 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (116 36 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (100 100 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (100 100 (:REWRITE SET::IN-SET))
 (94 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (84 2 (:DEFINITION TRUE-LIST-LISTP))
 (72 72 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (50 50 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (42 4 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (38 4 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (36 36 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (36 4 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (28 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (24 4 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (22 22 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (20 20 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (20 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 1))
 (20 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (18 6 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (14 7 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (14 4 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (13 13 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 2 (:REWRITE VL::CONSP-OF-CAR-WHEN-VL-COMMENTMAP-P))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (8 8 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (8 8 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (8 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (8 2 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (8 2 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (6 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (5 5 (:TYPE-PRESCRIPTION VL::VL-ELABSCOPES-INIT))
 (5 5 (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-SCANNEDALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VLS-LOADEDALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPOCANDIDATES-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-RESERVEDTABLE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDMERGEALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LUCIDDB-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPERHS-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DUPEINST-ALISTP . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-USE-SET-SUMMARIES-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-SD-PATALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SCOPETREE-ALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-RANGEMAP-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-PATH-ALIST-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-NAME-ALIST-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 1))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 2))
 (5 5 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-ADDRESS-ALIST-P . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 4 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (4 4 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (4 4 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (4 4 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (4 4 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL::CHARACTER-LISTP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LIST-LISTP))
 (4 4 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (4 2 (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (4 2 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE VL::CHARACTER-LISTP-OF-CAR-WHEN-CHARACTER-LIST-LISTP))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (2 2 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 (2 2 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 )
