(TYPES::WEAK-FORWARD-CHAIN-OR
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-FNS::SAFE-WITNESS))
 )
(TYPES::SYMBOLP-NATP-TRUE-LISTP-T-TRUE-LISTP-T-IMPLIES-TRUE-LISTP-WEAK-FORWARD-CHAIN-OR)
(TYPES::WEAK-FORWARD-CHAIN-OR)
(TYPES::BODY-IMPLIES-TERM)
(TYPES::PSEUDO-TERMP-PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-BODY-IMPLIES-TERM
 (61 9 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (43 9 (:DEFINITION SYMBOL-LISTP))
 (28 28 (:REWRITE DEFAULT-CAR))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (25 25 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 1 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::BODY-IMPLIES-TERM)
(TYPES::TERM-IMPLIES-BODY)
(TYPES::PSEUDO-TERMP-PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-TERM-IMPLIES-BODY
 (71 9 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (53 11 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:REWRITE DEFAULT-CAR))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (25 25 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 1 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::TERM-IMPLIES-BODY)
(TYPES::NOT-TERM-IMPLIES-NOT-BODY)
(TYPES::PSEUDO-TERMP-PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-NOT-TERM-IMPLIES-NOT-BODY
 (71 9 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (53 11 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:REWRITE DEFAULT-CAR))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (25 25 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 1 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::NOT-TERM-IMPLIES-NOT-BODY)
(TYPES::NOT-BODY-IMPLIES-NOT-TERM)
(TYPES::PSEUDO-TERMP-PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-NOT-BODY-IMPLIES-NOT-TERM
 (61 9 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (43 9 (:DEFINITION SYMBOL-LISTP))
 (28 28 (:REWRITE DEFAULT-CAR))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (25 25 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 1 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::NOT-BODY-IMPLIES-NOT-TERM)
(TYPES::TRUE-PSEUDO-TERMP)
(TYPES::FALSE-PSEUDO-TERMP)
(TYPES::DROP-NOTS
 (68 24 (:REWRITE DEFAULT-+-2))
 (38 24 (:REWRITE DEFAULT-+-1))
 (16 4 (:DEFINITION INTEGER-ABS))
 (16 2 (:DEFINITION LENGTH))
 (12 12 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 5 (:REWRITE DEFAULT-<-2))
 (7 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(TYPES::T-PSEUDO-TERMP-IMPLIES-PSEUDO-TERMP-DROP-NOTS
 (1768 1768 (:REWRITE DEFAULT-CDR))
 (1090 1090 (:REWRITE DEFAULT-CAR))
 (864 108 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (540 54 (:DEFINITION TRUE-LISTP))
 (464 232 (:REWRITE DEFAULT-+-2))
 (232 232 (:REWRITE DEFAULT-+-1))
 (216 216 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (216 108 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (216 108 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (156 156 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (108 108 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (108 108 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (108 108 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (108 108 (:REWRITE SET::IN-SET))
 )
(TYPES::DROP-NOTS
 (11 3 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(TYPES::NEGATE-TERM)
(TYPES::PSEUDO-TERMP-IMPLIES-PSEUDO-TERMP-NEGATE-TERM)
(TYPES::NEGATE-TERM)
(TYPES::NEGATE-TERM-LIST)
(TYPES::PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP-NEGATE-TERM-LIST
 (290 28 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (252 3 (:DEFINITION PSEUDO-TERMP))
 (223 35 (:DEFINITION SYMBOL-LISTP))
 (151 151 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (96 94 (:REWRITE DEFAULT-CDR))
 (95 93 (:REWRITE DEFAULT-CAR))
 (48 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (45 9 (:DEFINITION LEN))
 (33 3 (:DEFINITION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION LEN))
 (28 28 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (20 20 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 9 (:REWRITE DEFAULT-+-2))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 6 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(TYPES::NEGATE-TERM-LIST
 (76 1 (:DEFINITION PSEUDO-TERMP))
 (52 5 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (41 7 (:DEFINITION SYMBOL-LISTP))
 (28 28 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (24 24 (:REWRITE DEFAULT-CDR))
 (23 23 (:REWRITE DEFAULT-CAR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 1 (:DEFINITION TRUE-LISTP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::NOT-)
(TYPES::T-IMPLIES-SYMBOLP-NOT-)
(TYPES::NOT-)
(TYPES::COMMON-RULE-EVENTS
 (40 40 (:TYPE-PRESCRIPTION SYMBOL-FNS::SAFE-WITNESS))
 )
(TYPES::SYMBOLP-SYMBOLP-PSEUDO-TERMP-PSEUDO-TERM-LISTP-T-KWARGS-ALISTP-IMPLIES-TRUE-LISTP-COMMON-RULE-EVENTS)
(TYPES::COMMON-RULE-EVENTS
 (15387 15055 (:REWRITE DEFAULT-CAR))
 (13573 13241 (:REWRITE DEFAULT-CDR))
 (10910 5432 (:REWRITE DEFAULT-COERCE-1))
 (8041 897 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (7374 1389 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (7173 1389 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (6907 6907 (:REWRITE DEFAULT-COERCE-2))
 (6431 1475 (:REWRITE DEFAULT-COERCE-3))
 (6255 1192 (:DEFINITION SYMBOL-LISTP))
 (4784 598 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4485 897 (:DEFINITION LEN))
 (2990 299 (:DEFINITION TRUE-LISTP))
 (1794 897 (:REWRITE DEFAULT-+-2))
 (1330 740 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (1196 1196 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1196 598 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (1196 598 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1180 1180 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (1180 590 (:REWRITE DEFAULT-PKG-IMPORTS))
 (897 897 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (897 897 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (897 897 (:REWRITE DEFAULT-+-1))
 (598 598 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (598 598 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (598 598 (:REWRITE SET::IN-SET))
 (438 146 (:DEFINITION TYPES::NEGATE-TERM-LIST))
 )
(TYPES::PREDICATE-TYPE-SPECIFIER)
(TYPES::RULE-EVENTS)
(TYPES::SYMBOLP-SYMBOLP-PSEUDO-TERMP-PSEUDO-TERM-LISTP-PREDICATE-TYPE-SPECIFIER-KWARGS-ALISTP-IMPLIES-TRUE-LISTP-RULE-EVENTS)
(TYPES::RULE-EVENTS)
(TYPES::EVER-SET)
(TYPES::NOT-LIST)
(TYPES::AND-OR-P)
(TYPES::LIST-FIX)
(TYPES::T-IMPLIES-TRUE-LISTP-LIST-FIX)
(TYPES::LIST-FIX)
(TYPES::AND-OR-TYPE)
(TYPES::T-IMPLIES-PREDICATE-TYPE-SPECIFIER-AND-OR-TYPE
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(TYPES::AND-OR-TYPE)
(TYPES::AND-OR-BODY)
(TYPES::AND-OR-P-IMPLIES-PSEUDO-TERM-LISTP-AND-OR-BODY
 (36 36 (:REWRITE DEFAULT-CAR))
 (33 33 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (15 3 (:DEFINITION LEN))
 (10 10 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 1 (:DEFINITION TRUE-LISTP))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(TYPES::AND-OR-BODY)
(TYPES::UNARY-FUNCTION)
(TYPES::FIX-WEAK-PSEUDO-TERM)
(TYPES::MAKE-BODY-FROM-TYPE-NAME-LIST)
(TYPES::MAKE-PREDICATE-BODY)
(TYPES::DEF-TYPE-PREDICATE)
(TYPES::DEF-TYPE-PROPERTIES)
(TYPES::DEF-TYPE-PROPERTIES-WRAPPER)
(TYPES::DEF-TYPE-PREDICATE-WRAPPER)
(TYPES::DEF-TYPE-FN
 (8022 1337 (:DEFINITION TYPES::ASSOC-KEYWORD!))
 (4735 4735 (:REWRITE DEFAULT-CAR))
 (4710 4710 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(TYPES::PREFER-GUARDED)
(TYPES::DEF-TYPE-FN-WRAPPER)
