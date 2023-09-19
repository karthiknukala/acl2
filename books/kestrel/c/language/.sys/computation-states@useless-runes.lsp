(C::UPDATE-NTH-OF-REV
 (2503 113 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (1803 44 (:DEFINITION UPDATE-NTH))
 (1434 109 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (673 105 (:REWRITE NTH-WHEN-ZP))
 (462 80 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (427 16 (:REWRITE NTH-OF-REV))
 (410 96 (:REWRITE REV-WHEN-NOT-CONSP))
 (188 82 (:REWRITE NFIX-WHEN-NATP))
 (127 94 (:REWRITE NTH-WHEN-ATOM))
 (106 106 (:TYPE-PRESCRIPTION NATP))
 (56 44 (:REWRITE <-+-NEGATIVE-0-1))
 (36 2 (:REWRITE REPEAT-WHEN-ZP))
 (22 2 (:REWRITE CONSP-OF-REPEAT))
 (17 5 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 (15 15 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (7 7 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE <-+-NEGATIVE-0-2))
 )
(C::NTH-OF-MINUS1-AND-CDR
 (62 6 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (36 6 (:REWRITE NTH-WHEN-ZP))
 (32 32 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (21 7 (:REWRITE ZP-OPEN))
 (13 6 (:REWRITE NFIX-WHEN-NATP-CHEAP))
 (7 7 (:REWRITE <-0-+-NEGATIVE-1))
 (6 6 (:REWRITE NTH-WHEN-ATOM))
 (6 2 (:REWRITE NFIX-WHEN-NATP))
 (5 5 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE NATP-RW))
 )
(C::SCOPEP)
(C::BOOLEANP-OF-SCOPEP
 (8 2 (:DEFINITION C::SCOPEP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 (2 2 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::MAPP-WHEN-SCOPEP
 (184 55 (:REWRITE <<-TRICHOTOMY))
 (150 30 (:REWRITE <<-ASYMMETRIC))
 (72 18 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (64 52 (:REWRITE <<-TRANSITIVE))
 (44 12 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (38 38 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (18 18 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (18 18 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (16 8 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (3 3 (:REWRITE <<-IRREFLEXIVE))
 )
(C::SCOPEP-OF-TAIL
 (63 18 (:REWRITE <<-TRICHOTOMY))
 (52 10 (:REWRITE <<-ASYMMETRIC))
 (24 6 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (21 17 (:REWRITE <<-TRANSITIVE))
 (16 16 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (6 6 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (6 6 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (6 2 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (1 1 (:REWRITE <<-IRREFLEXIVE))
 )
(C::IDENTP-OF-HEAD-KEY-WHEN-SCOPEP
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (12 3 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (10 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (9 9 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (7 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (6 6 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (1 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(C::VALUEP-OF-HEAD-VAL-WHEN-SCOPEP
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (24 5 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (15 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (10 10 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (8 8 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (8 2 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (2 2 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (1 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(C::SCOPEP-OF-UPDATE
 (584 584 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (578 578 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (428 94 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (418 146 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (254 86 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (238 238 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (147 55 (:REWRITE OMAP::UPDATE-WHEN-EMPTY))
 (94 94 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (60 16 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:REWRITE-QUOTED-CONSTANT TRUE-LIST-LIST-FIX-UNDER-TRUE-LIST-LIST-EQUIV))
 )
(C::SCOPEP-OF-UPDATE*
 (228 60 (:REWRITE <<-TRICHOTOMY))
 (204 36 (:REWRITE <<-ASYMMETRIC))
 (126 24 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (90 12 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (60 60 (:REWRITE <<-TRANSITIVE))
 (54 12 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (48 48 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (22 22 (:TYPE-PRESCRIPTION OMAP::UPDATE*))
 (18 6 (:REWRITE OMAP::UPDATE*-WHEN-RIGHT-EMPTY))
 (12 12 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (12 12 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (9 3 (:REWRITE OMAP::UPDATE-WHEN-EMPTY))
 (9 3 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION FAST-<<))
 (5 5 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (3 3 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (3 3 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (2 2 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 )
(C::SCOPEP-OF-DELETE
 (324 11 (:DEFINITION C::SCOPEP))
 (175 7 (:REWRITE FAST-<<-IS-<<))
 (133 35 (:REWRITE <<-TRICHOTOMY))
 (119 21 (:REWRITE <<-ASYMMETRIC))
 (84 84 (:TYPE-PRESCRIPTION <<))
 (70 14 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (49 7 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (48 46 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (35 35 (:REWRITE <<-TRANSITIVE))
 (28 28 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (28 7 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (21 21 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (14 14 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (14 6 (:REWRITE OMAP::DELETE-WHEN-EMPTY))
 (9 3 (:REWRITE OMAP::UPDATE-WHEN-EMPTY))
 (7 7 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (7 7 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (6 6 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (5 5 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (4 4 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 )
(C::SCOPEP-OF-DELETE*
 (152 40 (:REWRITE <<-TRICHOTOMY))
 (136 24 (:REWRITE <<-ASYMMETRIC))
 (80 16 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (56 8 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (40 40 (:REWRITE <<-TRANSITIVE))
 (32 32 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (32 8 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (24 24 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (20 20 (:TYPE-PRESCRIPTION C::VALUEP))
 (18 6 (:REWRITE OMAP::DELETE*-WHEN-RIGHT-EMPTY))
 (16 16 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (9 3 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (9 3 (:REWRITE OMAP::DELETE-WHEN-EMPTY))
 (8 8 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (8 8 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (3 3 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (3 3 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE SET::TAIL-WHEN-EMPTY))
 )
(C::IDENTP-WHEN-IN-SCOPEP-BINDS-FREE-X
 (274 14 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (140 5 (:DEFINITION C::SCOPEP))
 (128 86 (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (92 76 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (75 3 (:REWRITE FAST-<<-IS-<<))
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (36 36 (:TYPE-PRESCRIPTION <<))
 (31 9 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (30 6 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (21 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (18 10 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (13 5 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (12 12 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 3 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (9 9 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (9 9 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (9 3 (:REWRITE C::MAPP-WHEN-SCOPEP))
 (8 8 (:TYPE-PRESCRIPTION C::VALUEP))
 (8 3 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (6 6 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (5 5 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (3 3 (:REWRITE C::SCOPEP-OF-TAIL))
 (3 3 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::IDENTP-OF-CAR-OF-IN-SCOPEP
 (283 15 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (235 7 (:DEFINITION C::SCOPEP))
 (165 121 (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (125 5 (:REWRITE FAST-<<-IS-<<))
 (116 100 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (95 25 (:REWRITE <<-TRICHOTOMY))
 (85 15 (:REWRITE <<-ASYMMETRIC))
 (80 9 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (60 60 (:TYPE-PRESCRIPTION <<))
 (50 10 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (37 15 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (35 5 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (28 12 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (25 25 (:REWRITE <<-TRANSITIVE))
 (21 9 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (20 20 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (20 12 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (18 18 (:TYPE-PRESCRIPTION C::IDENT-LISTP))
 (15 15 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (15 15 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (14 14 (:REWRITE C::IDENTP-WHEN-IN-SCOPEP-BINDS-FREE-X))
 (12 12 (:TYPE-PRESCRIPTION C::VALUEP))
 (11 11 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (9 3 (:REWRITE C::MAPP-WHEN-SCOPEP))
 (8 3 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (3 3 (:REWRITE C::SCOPEP-OF-TAIL))
 (2 2 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::VALUEP-OF-CDR-OF-IN-SCOPEP
 (283 15 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (235 7 (:DEFINITION C::SCOPEP))
 (196 152 (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (125 5 (:REWRITE FAST-<<-IS-<<))
 (115 99 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (95 25 (:REWRITE <<-TRICHOTOMY))
 (85 15 (:REWRITE <<-ASYMMETRIC))
 (60 60 (:TYPE-PRESCRIPTION <<))
 (37 15 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (32 32 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (28 12 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (25 25 (:REWRITE <<-TRANSITIVE))
 (20 12 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (20 5 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (15 15 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (11 11 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (9 4 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (9 3 (:REWRITE C::MAPP-WHEN-SCOPEP))
 (7 7 (:REWRITE C::IDENTP-WHEN-IN-SCOPEP-BINDS-FREE-X))
 (5 5 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (5 5 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::SCOPEP-OF-TAIL))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 (2 2 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::VALUEP-OF-LOOKUP-WHEN-SCOPEP
 (5 1 (:DEFINITION C::SCOPEP))
 (1 1 (:TYPE-PRESCRIPTION C::IDENTP))
 (1 1 (:TYPE-PRESCRIPTION FAST-<<))
 (1 1 (:REWRITE C::IDENTP-WHEN-IN-SCOPEP-BINDS-FREE-X))
 )
(C::SCOPE-FIX
 (1 1 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 )
(C::SCOPEP-OF-SCOPE-FIX)
(C::SCOPE-FIX-WHEN-SCOPEP
 (16 16 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 )
(C::EMPTY-SCOPE-FIX
 (4 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 )
(C::EMPTY-OF-SCOPE-FIX-TO-NOT-SCOPE-OR-EMPTY
 (8 8 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 (3 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (24 24 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 )
(C::SCOPE-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 )
(C::SCOPE-EQUIV-IS-AN-EQUIVALENCE)
(C::SCOPE-EQUIV-IMPLIES-EQUAL-SCOPE-FIX-1)
(C::SCOPE-FIX-UNDER-SCOPE-EQUIV)
(C::EQUAL-OF-SCOPE-FIX-1-FORWARD-TO-SCOPE-EQUIV)
(C::EQUAL-OF-SCOPE-FIX-2-FORWARD-TO-SCOPE-EQUIV)
(C::SCOPE-EQUIV-OF-SCOPE-FIX-1-FORWARD)
(C::SCOPE-EQUIV-OF-SCOPE-FIX-2-FORWARD)
(C::CDR-OF-IN-WHEN-SCOPEP
 (219 212 (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (104 94 (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (22 10 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (10 10 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (8 6 (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (6 6 (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (6 2 (:REWRITE C::MAPP-WHEN-SCOPEP))
 (5 5 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (4 4 (:REWRITE OMAP::IN-WHEN-EMPTY))
 )
(C::SCOPE-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(C::SCOPE-LISTP-OF-CONS)
(C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP)
(C::SCOPE-LISTP-WHEN-NOT-CONSP)
(C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP)
(C::TRUE-LISTP-WHEN-SCOPE-LISTP-COMPOUND-RECOGNIZER)
(C::SCOPE-LISTP-OF-LIST-FIX)
(C::SCOPE-LISTP-OF-SFIX)
(C::SCOPE-LISTP-OF-INSERT)
(C::SCOPE-LISTP-OF-DELETE)
(C::SCOPE-LISTP-OF-MERGESORT)
(C::SCOPE-LISTP-OF-UNION)
(C::SCOPE-LISTP-OF-INTERSECT-1)
(C::SCOPE-LISTP-OF-INTERSECT-2)
(C::SCOPE-LISTP-OF-DIFFERENCE)
(C::SCOPE-LISTP-OF-DUPLICATED-MEMBERS)
(C::SCOPE-LISTP-OF-REV)
(C::SCOPE-LISTP-OF-APPEND)
(C::SCOPE-LISTP-OF-RCONS)
(C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP)
(C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL)
(C::SCOPE-LISTP-OF-SET-DIFFERENCE-EQUAL)
(C::SCOPE-LISTP-OF-INTERSECTION-EQUAL-1)
(C::SCOPE-LISTP-OF-INTERSECTION-EQUAL-2)
(C::SCOPE-LISTP-OF-UNION-EQUAL)
(C::SCOPE-LISTP-OF-TAKE)
(C::SCOPE-LISTP-OF-REPEAT)
(C::SCOPEP-OF-NTH-WHEN-SCOPE-LISTP)
(C::SCOPE-LISTP-OF-UPDATE-NTH)
(C::SCOPE-LISTP-OF-BUTLAST)
(C::SCOPE-LISTP-OF-NTHCDR)
(C::SCOPE-LISTP-OF-LAST)
(C::SCOPE-LISTP-OF-REMOVE)
(C::SCOPE-LISTP-OF-REVAPPEND)
(C::SCOPE-LIST-FIX$INLINE
 (1 1 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 )
(C::SCOPE-LISTP-OF-SCOPE-LIST-FIX
 (30 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (22 2 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (18 10 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION C::SCOPE-LISTP))
 (12 6 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (12 5 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION C::SCOPEP))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (2 1 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 )
(C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP
 (32 4 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (28 24 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (13 3 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (9 6 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 )
(C::SCOPE-LIST-FIX$INLINE
 (8 8 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (6 1 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (4 4 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (2 2 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 )
(C::SCOPE-LIST-EQUIV$INLINE)
(C::SCOPE-LIST-EQUIV-IS-AN-EQUIVALENCE)
(C::SCOPE-LIST-EQUIV-IMPLIES-EQUAL-SCOPE-LIST-FIX-1)
(C::SCOPE-LIST-FIX-UNDER-SCOPE-LIST-EQUIV)
(C::EQUAL-OF-SCOPE-LIST-FIX-1-FORWARD-TO-SCOPE-LIST-EQUIV)
(C::EQUAL-OF-SCOPE-LIST-FIX-2-FORWARD-TO-SCOPE-LIST-EQUIV)
(C::SCOPE-LIST-EQUIV-OF-SCOPE-LIST-FIX-1-FORWARD)
(C::SCOPE-LIST-EQUIV-OF-SCOPE-LIST-FIX-2-FORWARD)
(C::CAR-OF-SCOPE-LIST-FIX-X-UNDER-SCOPE-EQUIV
 (33 3 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (18 3 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (18 2 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (12 12 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION C::SCOPEP))
 (6 6 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (6 6 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION C::SCOPE-LIST-FIX$INLINE))
 )
(C::CAR-SCOPE-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-SCOPE-EQUIV)
(C::CDR-OF-SCOPE-LIST-FIX-X-UNDER-SCOPE-LIST-EQUIV
 (41 3 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (22 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (20 20 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (12 2 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION C::SCOPEP))
 (4 4 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::CDR-SCOPE-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-SCOPE-LIST-EQUIV)
(C::CONS-OF-SCOPE-FIX-X-UNDER-SCOPE-LIST-EQUIV
 (34 4 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (17 2 (:REWRITE C::SCOPE-LISTP-OF-CONS))
 (10 10 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (5 5 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 )
(C::CONS-SCOPE-EQUIV-CONGRUENCE-ON-X-UNDER-SCOPE-LIST-EQUIV)
(C::CONS-OF-SCOPE-LIST-FIX-Y-UNDER-SCOPE-LIST-EQUIV
 (20 2 (:REWRITE C::SCOPE-LISTP-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION C::SCOPEP))
 (8 8 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (8 8 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (5 4 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 )
(C::CONS-SCOPE-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-SCOPE-LIST-EQUIV)
(C::CONSP-OF-SCOPE-LIST-FIX
 (18 2 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (11 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (8 8 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (8 8 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (6 1 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (4 4 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPEP))
 (2 2 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::SCOPE-LIST-FIX-UNDER-IFF
 (18 2 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (11 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (8 8 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (8 8 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (6 1 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (4 4 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPEP))
 (2 2 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::SCOPE-LIST-FIX-OF-CONS
 (21 3 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (9 1 (:REWRITE C::SCOPE-LISTP-OF-CONS))
 (6 6 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (4 4 (:TYPE-PRESCRIPTION C::SCOPEP))
 (4 4 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (4 4 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (3 3 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 )
(C::LEN-OF-SCOPE-LIST-FIX
 (35 4 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (14 14 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (12 2 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (11 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (7 7 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPEP))
 (2 2 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(C::SCOPE-LIST-FIX-OF-APPEND
 (114 10 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (58 2 (:REWRITE C::SCOPE-LISTP-OF-APPEND))
 (40 36 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (29 29 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (24 2 (:REWRITE C::SCOPE-LISTP-OF-LIST-FIX))
 (22 16 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (14 4 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (12 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (6 1 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPEP))
 (2 2 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::SCOPE-LIST-FIX-OF-REPEAT
 (20 2 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (16 4 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (12 2 (:REWRITE C::SCOPE-LISTP-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION C::SCOPEP))
 (10 10 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (1 1 (:REWRITE-QUOTED-CONSTANT C::SCOPE-LIST-FIX-UNDER-SCOPE-LIST-EQUIV))
 )
(C::LIST-EQUIV-REFINES-SCOPE-LIST-EQUIV
 (146 14 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (112 8 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (88 18 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (72 72 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (72 8 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (70 70 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (36 36 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION C::SCOPEP))
 (16 16 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::NTH-OF-SCOPE-LIST-FIX
 (250 22 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (166 23 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (102 102 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (97 97 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (80 15 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (74 7 (:REWRITE C::SCOPEP-OF-NTH-WHEN-SCOPE-LISTP))
 (66 11 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (51 51 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (44 44 (:TYPE-PRESCRIPTION C::SCOPEP))
 (44 44 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::SCOPE-LIST-EQUIV-IMPLIES-SCOPE-LIST-EQUIV-APPEND-1
 (269 32 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (205 17 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (128 128 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (126 126 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (120 17 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (117 22 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (64 64 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (34 34 (:TYPE-PRESCRIPTION C::SCOPEP))
 (34 34 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::SCOPE-LIST-EQUIV-IMPLIES-SCOPE-LIST-EQUIV-APPEND-2
 (393 46 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (322 26 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (204 39 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (192 26 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (190 190 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (189 189 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (95 95 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION C::SCOPEP))
 (52 52 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (4 4 (:REWRITE C::CONSP-OF-SCOPE-LIST-FIX))
 )
(C::SCOPE-LIST-EQUIV-IMPLIES-SCOPE-LIST-EQUIV-NTHCDR-2
 (298 20 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (208 39 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (198 198 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (198 20 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION C::SCOPEP))
 (40 40 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 )
(C::SCOPE-LIST-EQUIV-IMPLIES-SCOPE-LIST-EQUIV-TAKE-2
 (545 38 (:REWRITE C::SCOPE-LIST-FIX-WHEN-SCOPE-LISTP))
 (428 28 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (300 51 (:REWRITE C::SCOPE-LISTP-OF-CDR-WHEN-SCOPE-LISTP))
 (292 26 (:REWRITE C::SCOPEP-OF-CAR-WHEN-SCOPE-LISTP))
 (236 236 (:TYPE-PRESCRIPTION C::SCOPE-LISTP))
 (236 236 (:REWRITE C::SCOPE-LISTP-WHEN-SUBSETP-EQUAL))
 (217 24 (:REWRITE C::SCOPE-LISTP-OF-TAKE))
 (136 118 (:REWRITE C::SCOPE-LISTP-WHEN-NOT-CONSP))
 (66 66 (:TYPE-PRESCRIPTION C::SCOPEP))
 (66 66 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT C::SCOPE-LIST-FIX-UNDER-SCOPE-LIST-EQUIV))
 (6 6 (:DEFINITION NFIX))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::SCOPE-RESULTP)
(C::CONSP-WHEN-SCOPE-RESULTP)
(C::SCOPE-RESULT-KIND$INLINE)
(C::SCOPE-RESULT-KIND-POSSIBILITIES)
(C::SCOPE-RESULT-FIX$INLINE
 (1 1 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 )
(C::SCOPE-RESULTP-OF-SCOPE-RESULT-FIX
 (21 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (13 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (1 1 (:TYPE-PRESCRIPTION C::ERRORP))
 )
(C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::SCOPE-RESULT-FIX$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (24 24 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 )
(C::SCOPE-RESULT-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 )
(C::SCOPE-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(C::SCOPE-RESULT-EQUIV-IMPLIES-EQUAL-SCOPE-RESULT-FIX-1)
(C::SCOPE-RESULT-FIX-UNDER-SCOPE-RESULT-EQUIV)
(C::EQUAL-OF-SCOPE-RESULT-FIX-1-FORWARD-TO-SCOPE-RESULT-EQUIV)
(C::EQUAL-OF-SCOPE-RESULT-FIX-2-FORWARD-TO-SCOPE-RESULT-EQUIV)
(C::SCOPE-RESULT-EQUIV-OF-SCOPE-RESULT-FIX-1-FORWARD)
(C::SCOPE-RESULT-EQUIV-OF-SCOPE-RESULT-FIX-2-FORWARD)
(C::SCOPE-RESULT-KIND$INLINE-OF-SCOPE-RESULT-FIX-X
 (221 13 (:REWRITE C::IDENTP-WHEN-WRONG-TAG))
 (13 13 (:REWRITE C::TAG-WHEN-TYNAMEP))
 (13 13 (:REWRITE C::TAG-WHEN-TRANSUNITP))
 (13 13 (:REWRITE C::TAG-WHEN-STRUCT-DECLONP))
 (13 13 (:REWRITE FTY::TAG-WHEN-RESERRP))
 (13 13 (:REWRITE C::TAG-WHEN-PARAM-DECLONP))
 (13 13 (:REWRITE C::TAG-WHEN-OBJ-DECLONP))
 (13 13 (:REWRITE C::TAG-WHEN-MEMBER-VALUEP))
 (13 13 (:REWRITE C::TAG-WHEN-MEMBER-TYPEP))
 (13 13 (:REWRITE C::TAG-WHEN-IDENTP))
 (13 13 (:REWRITE C::TAG-WHEN-ICONSTP))
 (13 13 (:REWRITE C::TAG-WHEN-FUNDEFP))
 (13 13 (:REWRITE C::TAG-WHEN-FUN-DECLONP))
 (13 13 (:REWRITE C::TAG-WHEN-FILESETP))
 (13 13 (:REWRITE C::TAG-WHEN-FILEP))
 (13 13 (:REWRITE C::TAG-WHEN-ERRORP))
 (13 13 (:REWRITE C::TAG-WHEN-ADDRESSP))
 (6 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (5 1 (:DEFINITION C::ERRORP))
 (2 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::SCOPE-RESULT-KIND$INLINE-SCOPE-RESULT-EQUIV-CONGRUENCE-ON-X)
(C::SCOPE-RESULT-OK->GET$INLINE
 (1 1 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 )
(C::SCOPEP-OF-SCOPE-RESULT-OK->GET
 (20 2 (:DEFINITION C::SCOPEP))
 (16 1 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (9 1 (:DEFINITION C::SCOPE-FIX))
 (3 3 (:TYPE-PRESCRIPTION C::VALUEP))
 (3 3 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 (3 3 (:TYPE-PRESCRIPTION C::IDENTP))
 (3 3 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::SCOPE-RESULT-OK->GET$INLINE-OF-SCOPE-RESULT-FIX-X
 (109 109 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (54 18 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (36 36 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 (26 16 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 (24 16 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 )
(C::SCOPE-RESULT-OK->GET$INLINE-SCOPE-RESULT-EQUIV-CONGRUENCE-ON-X)
(C::SCOPE-RESULT-OK->GET-WHEN-WRONG-KIND
 (12 12 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 )
(C::SCOPE-RESULT-OK
 (4 1 (:DEFINITION C::SCOPEP))
 (1 1 (:TYPE-PRESCRIPTION C::VALUEP))
 (1 1 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (1 1 (:TYPE-PRESCRIPTION C::IDENTP))
 (1 1 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::RETURN-TYPE-OF-SCOPE-RESULT-OK
 (26 2 (:REWRITE C::SCOPE-FIX-WHEN-SCOPEP))
 (15 15 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 (10 10 (:TYPE-PRESCRIPTION C::VALUEP))
 (10 10 (:TYPE-PRESCRIPTION C::IDENTP))
 (10 10 (:TYPE-PRESCRIPTION FAST-<<))
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::SCOPE-RESULT-OK->GET-OF-SCOPE-RESULT-OK
 (68 68 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (27 27 (:TYPE-PRESCRIPTION C::SCOPE-FIX))
 (16 8 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 )
(C::SCOPE-RESULT-OK-OF-FIELDS
 (52 7 (:DEFINITION C::SCOPEP))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (10 10 (:TYPE-PRESCRIPTION C::VALUEP))
 (10 10 (:TYPE-PRESCRIPTION C::IDENTP))
 (10 10 (:TYPE-PRESCRIPTION FAST-<<))
 (6 3 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (3 1 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 )
(C::SCOPE-RESULT-FIX-WHEN-OK
 (42 6 (:DEFINITION C::SCOPEP))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (8 8 (:TYPE-PRESCRIPTION C::VALUEP))
 (8 8 (:TYPE-PRESCRIPTION C::IDENTP))
 (8 8 (:TYPE-PRESCRIPTION FAST-<<))
 (6 3 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (3 1 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 )
(C::EQUAL-OF-SCOPE-RESULT-OK)
(C::SCOPE-RESULT-OK-OF-SCOPE-FIX-GET
 (42 6 (:DEFINITION C::SCOPEP))
 (9 6 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (8 8 (:TYPE-PRESCRIPTION C::VALUEP))
 (8 8 (:TYPE-PRESCRIPTION C::IDENTP))
 (8 8 (:TYPE-PRESCRIPTION FAST-<<))
 )
(C::SCOPE-RESULT-OK-SCOPE-EQUIV-CONGRUENCE-ON-GET)
(C::SCOPE-RESULT-ERR->GET$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::ERRORP-OF-SCOPE-RESULT-ERR->GET
 (93 3 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (15 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::SCOPE-RESULT-ERR->GET$INLINE-OF-SCOPE-RESULT-FIX-X
 (186 10 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (166 10 (:DEFINITION C::ERRORP))
 (84 20 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (72 72 (:TYPE-PRESCRIPTION STRIP-CARS))
 (38 8 (:DEFINITION ALISTP))
 (33 11 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (28 28 (:TYPE-PRESCRIPTION ALISTP))
 (22 22 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 (21 21 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (10 10 (:TYPE-PRESCRIPTION C::ERRORP))
 (7 7 (:DEFINITION STRIP-CARS))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 )
(C::SCOPE-RESULT-ERR->GET$INLINE-SCOPE-RESULT-EQUIV-CONGRUENCE-ON-X)
(C::SCOPE-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (1 1 (:TYPE-PRESCRIPTION C::ERRORP))
 (1 1 (:DEFINITION C::ERRORP))
 )
(C::SCOPE-RESULT-ERR
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::RETURN-TYPE-OF-SCOPE-RESULT-ERR)
(C::SCOPE-RESULT-ERR->GET-OF-SCOPE-RESULT-ERR
 (50 8 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (36 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (34 1 (:DEFINITION C::ERRORP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (9 1 (:DEFINITION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION C::ERRORP))
 )
(C::SCOPE-RESULT-ERR-OF-FIELDS
 (42 2 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (38 2 (:DEFINITION C::ERRORP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (10 4 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 2 (:DEFINITION ALISTP))
 (3 1 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION C::ERRORP))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(C::SCOPE-RESULT-FIX-WHEN-ERR
 (22 2 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (19 1 (:DEFINITION C::ERRORP))
 (13 13 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 1 (:DEFINITION ALISTP))
 (3 1 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 (1 1 (:TYPE-PRESCRIPTION C::ERRORP))
 (1 1 (:DEFINITION STRIP-CARS))
 )
(C::EQUAL-OF-SCOPE-RESULT-ERR
 (82 6 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
 (74 6 (:DEFINITION C::ERRORP))
 (29 23 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (20 6 (:DEFINITION ALISTP))
 (16 4 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (8 8 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (6 6 (:DEFINITION STRIP-CARS))
 (4 4 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION C::ERRORP))
 )
(C::SCOPE-RESULT-ERR-OF-ERROR-FIX-GET)
(C::SCOPE-RESULT-ERR-ERROR-EQUIV-CONGRUENCE-ON-GET)
(C::SCOPE-RESULT-FIX-REDEF
 (22 11 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK))
 (15 15 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-FIX$INLINE))
 (12 12 (:TYPE-PRESCRIPTION C::SCOPE-RESULT-OK->GET$INLINE))
 (9 3 (:REWRITE C::SCOPE-RESULT-FIX-WHEN-SCOPE-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION C::SCOPE-RESULTP))
 )
(C::SCOPE-RESULTP-WHEN-SCOPEP)
(C::SCOPE-RESULTP-WHEN-ERRORP)
(C::SCOPEP-WHEN-SCOPE-RESULTP-AND-NOT-ERRORP)
(C::NOT-ERRORP-WHEN-SCOPEP
 (20 5 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (10 10 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (10 10 (:REWRITE C::SCOPEP-WHEN-MEMBER-EQUAL-OF-SCOPE-LISTP))
 (5 5 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 )
