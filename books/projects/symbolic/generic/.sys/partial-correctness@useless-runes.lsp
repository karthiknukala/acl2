(NEXTT)
(RUN
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CUTPOINT)
(EXITPOINT)
(PRE)
(ASSERTION)
(POST)
(DEFAULT-STATE)
(|every exitpoint is a cutpoint|)
(|precondition implies assertion|)
(|precondition implies cutpoint|)
(|assertion at exitpoint implies postcondition|)
(|STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-test|)
(|STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-base|)
(|STEPS-TO-CUTPOINT-TAIL-arity-1-step|)
(|STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|STEPS-TO-CUTPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|))
 )
(|STEPS-TO-CUTPOINT-TAIL-arity-1-DEF|)
(STEPS-TO-CUTPOINT-TAIL)
(STEPS-TO-CUTPOINT-TAIL-DEF
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE |precondition implies cutpoint|))
 (1 1 (:TYPE-PRESCRIPTION PRE))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(STEPS-TO-CUTPOINT)
(NEXTT-CUTPOINT)
(|assertion invariant over cutpoints|)
(|STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-test|)
(|STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-base|)
(|STEPS-TO-EXITPOINT-TAIL-arity-1-step|)
(|STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|STEPS-TO-EXITPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|))
 )
(|STEPS-TO-EXITPOINT-TAIL-arity-1-DEF|)
(STEPS-TO-EXITPOINT-TAIL)
(STEPS-TO-EXITPOINT-TAIL-DEF
 (6 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(STEPS-TO-EXITPOINT)
(CUTPOINT-INDUCTION
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(STEPS-TO-CUTPOINT-TAIL-INV
 (116 116 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (108 95 (:REWRITE DEFAULT-+-2))
 (96 95 (:REWRITE DEFAULT-+-1))
 (82 34 (:REWRITE FOLD-CONSTS-IN-+))
 (76 13 (:REWRITE ZP-OPEN))
 (63 3 (:REWRITE NATP-POSP))
 (48 12 (:REWRITE <-0-+-NEGATIVE-1))
 (32 32 (:REWRITE |precondition implies cutpoint|))
 (31 31 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE DEFAULT-<-1))
 (29 5 (:REWRITE NATP-RW))
 (27 3 (:REWRITE POSP-RW))
 (24 6 (:REWRITE <-+-NEGATIVE-0-1))
 (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(STEPS-TO-CUTPOINT-IS-ORDINAL
 (10 2 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE |precondition implies cutpoint|))
 (4 1 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(STEPS-TO-CUTPOINT-IS-NATP
 (24 4 (:DEFINITION RUN))
 (12 4 (:REWRITE ZP-OPEN))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 6 (:REWRITE |precondition implies cutpoint|))
 (6 3 (:REWRITE NATP-RW))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-<-1))
 (4 2 (:DEFINITION STEPS-TO-CUTPOINT-TAIL-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(STEPS-TO-CUTPOINT-PROVIDE-CUTPOINT
 (36 5 (:DEFINITION RUN))
 (19 5 (:REWRITE ZP-OPEN))
 (8 7 (:REWRITE DEFAULT-+-2))
 (8 7 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE |precondition implies cutpoint|))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION OMEGA))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:DEFINITION STEPS-TO-CUTPOINT-TAIL-DEF))
 (2 2 (:REWRITE NATP-RW))
 )
(STEPS-TO-CUTPOINT-IS-MINIMAL
 (24 4 (:DEFINITION RUN))
 (12 4 (:REWRITE ZP-OPEN))
 (11 4 (:REWRITE DEFAULT-<-2))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 6 (:TYPE-PRESCRIPTION OMEGA))
 (6 6 (:REWRITE |precondition implies cutpoint|))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:DEFINITION STEPS-TO-CUTPOINT-TAIL-DEF))
 (2 2 (:REWRITE NATP-RW))
 )
(STEPS-TO-EXITPOINT-TAIL-INV
 (134 134 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (108 95 (:REWRITE DEFAULT-+-2))
 (96 95 (:REWRITE DEFAULT-+-1))
 (82 34 (:REWRITE FOLD-CONSTS-IN-+))
 (76 13 (:REWRITE ZP-OPEN))
 (63 3 (:REWRITE NATP-POSP))
 (48 12 (:REWRITE <-0-+-NEGATIVE-1))
 (32 32 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE DEFAULT-<-1))
 (30 6 (:REWRITE NATP-RW))
 (27 3 (:REWRITE POSP-RW))
 (24 6 (:REWRITE <-+-NEGATIVE-0-1))
 (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(STEPS-TO-EXITPOINT-IS-ORDINAL
 (10 2 (:REWRITE ZP-OPEN))
 (4 1 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 )
(STEPS-TO-EXITPOINT-IS-NATP
 (24 4 (:DEFINITION RUN))
 (12 4 (:REWRITE ZP-OPEN))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE NATP-RW))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-<-1))
 (4 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:DEFINITION STEPS-TO-EXITPOINT-TAIL-DEF))
 )
(STEPS-TO-EXITPOINT-PROVIDE-EXITPOINT
 (36 5 (:DEFINITION RUN))
 (19 5 (:REWRITE ZP-OPEN))
 (8 7 (:REWRITE DEFAULT-+-2))
 (8 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION OMEGA))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (3 3 (:REWRITE NATP-RW))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:DEFINITION STEPS-TO-EXITPOINT-TAIL-DEF))
 )
(STEPS-TO-EXITPOINT-IS-MINIMAL
 (24 4 (:DEFINITION RUN))
 (12 4 (:REWRITE ZP-OPEN))
 (11 4 (:REWRITE DEFAULT-<-2))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 6 (:TYPE-PRESCRIPTION OMEGA))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:DEFINITION STEPS-TO-EXITPOINT-TAIL-DEF))
 )
(BIG-STEP-RUN
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(BIG-STEP-INDUCTION
 (6 6 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(RUN+-REDUCTION
 (35 13 (:REWRITE ZP-OPEN))
 (24 22 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-+-1))
 (13 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (6 6 (:REWRITE NATP-RW))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(RUN-ALWAYS-EXPANDS
 (19 5 (:REWRITE ZP-OPEN))
 (9 7 (:REWRITE DEFAULT-+-2))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:DEFINITION NOT))
 )
(NO-BIG-EXITPOINT
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(CUTPOINT-IMPLIES-ASSERTION
 (537 43 (:DEFINITION RUN))
 (358 66 (:REWRITE ZP-OPEN))
 (152 114 (:REWRITE DEFAULT-+-2))
 (116 114 (:REWRITE DEFAULT-+-1))
 (80 20 (:REWRITE <-0-+-NEGATIVE-1))
 (68 68 (:META CANCEL_PLUS-LESSP-CORRECT))
 (65 25 (:REWRITE FOLD-CONSTS-IN-+))
 (56 48 (:REWRITE DEFAULT-<-2))
 (48 48 (:REWRITE DEFAULT-<-1))
 (46 16 (:REWRITE NATP-RW))
 (29 29 (:REWRITE |precondition implies assertion|))
 (15 15 (:REWRITE |precondition implies cutpoint|))
 (10 10 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (10 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BIG-STEP-IS-ALWAYS-A-CUTPOINT
 (350 67 (:REWRITE ZP-OPEN))
 (153 116 (:REWRITE DEFAULT-+-2))
 (120 116 (:REWRITE DEFAULT-+-1))
 (74 23 (:REWRITE NATP-RW))
 (68 17 (:REWRITE <-0-+-NEGATIVE-1))
 (66 66 (:META CANCEL_PLUS-LESSP-CORRECT))
 (57 23 (:REWRITE FOLD-CONSTS-IN-+))
 (56 49 (:REWRITE DEFAULT-<-2))
 (49 49 (:REWRITE DEFAULT-<-1))
 (37 37 (:REWRITE |precondition implies cutpoint|))
 (17 17 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (9 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NO-EXITPOINT-MEANS-NOT-EXITPOINT
 (68 4 (:DEFINITION NEXTT-CUTPOINT))
 (32 4 (:DEFINITION RUN))
 (28 12 (:REWRITE ZP-OPEN))
 (20 20 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (16 4 (:REWRITE NATP-RW))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (4 4 (:REWRITE RUN-ALWAYS-EXPANDS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(BIG-STEPS-ALTERNATE-DEFINITION
 (550 550 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (276 227 (:REWRITE DEFAULT-+-2))
 (227 227 (:REWRITE DEFAULT-+-1))
 (224 56 (:REWRITE NATP-RW))
 (139 139 (:META CANCEL_PLUS-LESSP-CORRECT))
 (108 108 (:REWRITE DEFAULT-<-2))
 (108 108 (:REWRITE DEFAULT-<-1))
 (73 73 (:REWRITE RUN-ALWAYS-EXPANDS))
 (56 56 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 )
(FIRST-EXITPOINT-HAS-ASSERTION-TOO
 (136 19 (:DEFINITION RUN))
 (91 31 (:REWRITE ZP-OPEN))
 (56 17 (:REWRITE NATP-RW))
 (37 37 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE DEFAULT-+-1))
 (19 19 (:REWRITE RUN-ALWAYS-EXPANDS))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
 (13 13 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (8 8 (:REWRITE |precondition implies assertion|))
 (6 6 (:REWRITE |precondition implies cutpoint|))
 )
(BIG-STEPS
 (93 93 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (43 3 (:REWRITE O<=-O-FINP-DEF))
 (25 16 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 11 (:REWRITE DEFAULT-<-1))
 (12 3 (:REWRITE NATP-RW))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 3 (:REWRITE O-INFP-O-FINP-O<=))
 (8 3 (:REWRITE AC-<))
 (7 1 (:REWRITE O-FIRST-EXPT-<))
 (5 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (5 1 (:REWRITE <-+-NEGATIVE-0-2))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
 (3 3 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (1 1 (:REWRITE O-FIRST-COEFF-<))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LITTLE-STEPS
 (6 6 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(BIG-STEPS-IS-NATP)
(LITTLE-STEPS-IS-NATP
 (126 126 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (113 46 (:REWRITE DEFAULT-+-2))
 (81 46 (:REWRITE DEFAULT-+-1))
 (64 15 (:REWRITE ZP-OPEN))
 (56 7 (:DEFINITION RUN))
 (47 12 (:REWRITE NATP-RW))
 (33 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (17 11 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 3 (:REWRITE <-0-+-NEGATIVE-1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (7 7 (:REWRITE RUN-ALWAYS-EXPANDS))
 (6 6 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 )
(CUTPOINT-IS-HIT-BY-BIG-STEPS
 (309 41 (:REWRITE ZP-OPEN))
 (199 98 (:REWRITE DEFAULT-+-2))
 (103 98 (:REWRITE DEFAULT-+-1))
 (66 16 (:REWRITE <-0-+-NEGATIVE-1))
 (54 54 (:META CANCEL_PLUS-LESSP-CORRECT))
 (51 38 (:REWRITE DEFAULT-<-2))
 (45 9 (:REWRITE NATP-RW))
 (38 38 (:REWRITE DEFAULT-<-1))
 (33 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (31 2 (:REWRITE ASSOCIATIVITY-OF-+))
 (28 1 (:REWRITE NATP-POSP))
 (13 1 (:REWRITE POSP-RW))
 (12 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE |precondition implies cutpoint|))
 (8 8 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 1 (:REWRITE O-INFP->NEQ-0))
 )
(FIRST-EXITPOINT-IS-HIT-BY-BIG-STEPS
 (102 2 (:DEFINITION BIG-STEPS))
 (100 10 (:DEFINITION RUN))
 (94 14 (:REWRITE ZP-OPEN))
 (68 4 (:DEFINITION NEXTT-CUTPOINT))
 (64 2 (:DEFINITION BIG-STEP-RUN))
 (30 18 (:REWRITE DEFAULT-+-2))
 (20 12 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE NATP-RW))
 (16 16 (:TYPE-PRESCRIPTION BIG-STEPS-IS-NATP))
 (16 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 10 (:REWRITE RUN-ALWAYS-EXPANDS))
 (8 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (4 1 (:LINEAR STEPS-TO-EXITPOINT-IS-MINIMAL))
 (4 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |precondition implies cutpoint|))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NO-EXITPOINT
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(NO-EXITPOINT-IMPLIES-NOT-EXITPOINT
 (29 29 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (8 8 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE NATP-RW))
 (5 5 (:REWRITE RUN-ALWAYS-EXPANDS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:REWRITE O-INFP->NEQ-0))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NO-EXITPOINT-MEANS-NO-EXITPOINT
 (25 25 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (9 9 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE NATP-RW))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(NO-EXITPOINT-FOR-RUN
 (33 12 (:REWRITE ZP-OPEN))
 (28 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (25 25 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (25 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (12 3 (:REWRITE <-0-+-NEGATIVE-2))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE NO-EXITPOINT-IMPLIES-NOT-EXITPOINT))
 (5 5 (:REWRITE RUN-ALWAYS-EXPANDS))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(LITTLE-BIG-INVERSE
 (429 212 (:REWRITE DEFAULT-+-2))
 (321 52 (:REWRITE ZP-OPEN))
 (121 22 (:REWRITE NATP-RW))
 (113 5 (:REWRITE NATP-POSP))
 (91 91 (:META CANCEL_PLUS-LESSP-CORRECT))
 (76 65 (:REWRITE DEFAULT-<-2))
 (70 65 (:REWRITE DEFAULT-<-1))
 (68 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (61 15 (:REWRITE <-0-+-NEGATIVE-1))
 (53 5 (:REWRITE POSP-RW))
 (50 50 (:REWRITE RUN-ALWAYS-EXPANDS))
 (35 7 (:REWRITE <-+-NEGATIVE-0-2))
 (21 21 (:REWRITE |precondition implies cutpoint|))
 (20 4 (:REWRITE <-0-+-NEGATIVE-2))
 (17 17 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:REWRITE EQUAL-CONSTANT-+))
 (2 1 (:REWRITE O-INFP->NEQ-0))
 )
(LITTLE-STEPS-BIT-STEPS
 (177 177 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (137 59 (:REWRITE DEFAULT-+-2))
 (98 59 (:REWRITE DEFAULT-+-1))
 (88 11 (:DEFINITION RUN))
 (44 11 (:REWRITE NATP-RW))
 (37 15 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
 (17 11 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (16 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (13 6 (:REWRITE O-INFP->NEQ-0))
 (12 3 (:REWRITE <-0-+-NEGATIVE-1))
 (11 11 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (11 11 (:REWRITE RUN-ALWAYS-EXPANDS))
 (9 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (1 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 )
(BIG-STEPS-IS-LITTLE-STEPS
 (1286 170 (:REWRITE ZP-OPEN))
 (1069 515 (:REWRITE DEFAULT-+-2))
 (699 515 (:REWRITE DEFAULT-+-1))
 (284 191 (:REWRITE DEFAULT-<-2))
 (235 235 (:META CANCEL_PLUS-LESSP-CORRECT))
 (195 191 (:REWRITE DEFAULT-<-1))
 (177 48 (:REWRITE NATP-RW))
 (176 44 (:REWRITE <-0-+-NEGATIVE-1))
 (175 73 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (39 39 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (28 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (28 1 (:REWRITE NATP-POSP))
 (13 1 (:REWRITE POSP-RW))
 (12 12 (:REWRITE |precondition implies cutpoint|))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LITTLE-IS-MONOTONIC
 (249 249 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (196 71 (:REWRITE DEFAULT-+-2))
 (138 71 (:REWRITE DEFAULT-+-1))
 (80 10 (:DEFINITION RUN))
 (77 16 (:REWRITE ZP-OPEN))
 (62 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (49 19 (:REWRITE NATP-RW))
 (37 27 (:REWRITE DEFAULT-<-2))
 (35 35 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (32 27 (:REWRITE DEFAULT-<-1))
 (30 30 (:META CANCEL_PLUS-LESSP-CORRECT))
 (22 16 (:REWRITE FOLD-CONSTS-IN-+))
 (12 3 (:REWRITE <-0-+-NEGATIVE-1))
 (10 10 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (10 10 (:REWRITE RUN-ALWAYS-EXPANDS))
 (3 3 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 )
(BIG-STEP-ENCOUNTERS-NO-EXITPOINT
 (780 17 (:DEFINITION BIG-STEPS))
 (754 295 (:REWRITE DEFAULT-+-2))
 (664 10 (:REWRITE LITTLE-STEPS-BIT-STEPS))
 (500 5 (:DEFINITION BIG-STEP-RUN))
 (455 295 (:REWRITE DEFAULT-+-1))
 (228 81 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (224 62 (:REWRITE NATP-RW))
 (157 118 (:REWRITE DEFAULT-<-2))
 (136 17 (:REWRITE DEFAULT-UNARY-MINUS))
 (124 118 (:REWRITE DEFAULT-<-1))
 (123 123 (:META CANCEL_PLUS-LESSP-CORRECT))
 (74 74 (:REWRITE RUN-ALWAYS-EXPANDS))
 (64 54 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (51 17 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (20 5 (:REWRITE <-0-+-NEGATIVE-1))
 (15 15 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (15 15 (:REWRITE NO-EXITPOINT-IMPLIES-NOT-EXITPOINT))
 (9 9 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE |precondition implies cutpoint|))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(FALSIFIER-NO-EXITPOINT
 (5 5 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(FALSIFIER-IS-NATP-OR-OMEGA
 (68 4 (:DEFINITION NEXTT-CUTPOINT))
 (44 11 (:REWRITE NATP-RW))
 (32 4 (:DEFINITION RUN))
 (29 13 (:REWRITE ZP-OPEN))
 (20 20 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (13 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (6 4 (:REWRITE DEFAULT-CDR))
 (6 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (4 4 (:REWRITE RUN-ALWAYS-EXPANDS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(FALSIFIER-IF-NATP-IS-LESS-THAN-N
 (119 7 (:DEFINITION NEXTT-CUTPOINT))
 (83 26 (:REWRITE NATP-RW))
 (64 64 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (56 7 (:DEFINITION RUN))
 (45 17 (:REWRITE ZP-OPEN))
 (35 35 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (25 25 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-+-1))
 (19 19 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 15 (:REWRITE DEFAULT-<-1))
 (12 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (7 7 (:REWRITE RUN-ALWAYS-EXPANDS))
 )
(FALSIFIER-FALSIFIES-1
 (102 6 (:DEFINITION NEXTT-CUTPOINT))
 (60 18 (:REWRITE NATP-RW))
 (48 6 (:DEFINITION RUN))
 (41 17 (:REWRITE ZP-OPEN))
 (30 30 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (18 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (6 6 (:REWRITE RUN-ALWAYS-EXPANDS))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(FALSIFIER-FALSIFIES-2
 (2847 100 (:REWRITE ZP-OPEN))
 (2536 42 (:LINEAR LITTLE-IS-MONOTONIC))
 (949 358 (:REWRITE DEFAULT-+-2))
 (883 883 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (694 54 (:REWRITE ASSOCIATIVITY-OF-+))
 (623 358 (:REWRITE DEFAULT-+-1))
 (480 60 (:DEFINITION RUN))
 (265 107 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (232 58 (:REWRITE NATP-RW))
 (204 183 (:REWRITE DEFAULT-<-2))
 (195 195 (:META CANCEL_PLUS-LESSP-CORRECT))
 (183 183 (:REWRITE DEFAULT-<-1))
 (73 73 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (60 60 (:REWRITE RUN-ALWAYS-EXPANDS))
 (56 56 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (24 6 (:REWRITE <-0-+-NEGATIVE-1))
 (13 13 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (3 3 (:REWRITE BIG-STEP-ENCOUNTERS-NO-EXITPOINT))
 )
(LESS-THAN-EXITPOINT-IMPLIES-NO-EXITPOINT
 (1190 2 (:REWRITE LITTLE-STEPS-BIT-STEPS))
 (1155 55 (:REWRITE ZP-OPEN))
 (1040 10 (:LINEAR LITTLE-IS-MONOTONIC))
 (740 1 (:DEFINITION BIG-STEP-RUN))
 (589 12 (:DEFINITION LITTLE-STEPS))
 (539 14 (:DEFINITION FALSIFIER-NO-EXITPOINT))
 (266 126 (:REWRITE DEFAULT-+-2))
 (262 31 (:DEFINITION RUN))
 (226 41 (:REWRITE FALSIFIER-IS-NATP-OR-OMEGA))
 (190 58 (:REWRITE NATP-RW))
 (186 126 (:REWRITE DEFAULT-+-1))
 (156 12 (:REWRITE ASSOCIATIVITY-OF-+))
 (75 65 (:REWRITE DEFAULT-<-2))
 (71 71 (:TYPE-PRESCRIPTION LITTLE-STEPS-IS-NATP))
 (69 69 (:META CANCEL_PLUS-LESSP-CORRECT))
 (65 65 (:REWRITE DEFAULT-<-1))
 (64 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (51 1 (:DEFINITION BIG-STEPS))
 (36 2 (:REWRITE LITTLE-BIG-INVERSE))
 (31 31 (:REWRITE RUN-ALWAYS-EXPANDS))
 (29 29 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (26 26 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (19 15 (:REWRITE FOLD-CONSTS-IN-+))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (8 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE |precondition implies cutpoint|))
 )
(NOT-EXITPOINT-TO-STEPS-NATP
 (12 8 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (7 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 (6 6 (:TYPE-PRESCRIPTION STEPS-TO-EXITPOINT-IS-NATP))
 (3 3 (:REWRITE RUN-ALWAYS-EXPANDS))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NO-EXITPOINT-IMPLIES-NOT-EXITPOINT))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(BIG-STEPS-IS-NATP->0
 (266 266 (:TYPE-PRESCRIPTION STEPS-TO-CUTPOINT-IS-NATP))
 (225 75 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (61 4 (:REWRITE NATP-POSP))
 (43 4 (:REWRITE POSP-RW))
 (34 2 (:DEFINITION NEXTT-CUTPOINT))
 (33 15 (:REWRITE DEFAULT-+-2))
 (32 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (26 8 (:REWRITE NATP-RW))
 (18 11 (:REWRITE DEFAULT-<-2))
 (16 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 2 (:DEFINITION RUN))
 (15 15 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 2 (:REWRITE ZP-OPEN))
 (6 3 (:REWRITE O-INFP->NEQ-0))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (2 2 (:REWRITE RUN-ALWAYS-EXPANDS))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:LINEAR STEPS-TO-CUTPOINT-IS-MINIMAL))
 )
(|partial correctness|
 (664 24 (:LINEAR LITTLE-IS-MONOTONIC))
 (579 264 (:REWRITE DEFAULT-+-2))
 (344 264 (:REWRITE DEFAULT-+-1))
 (252 69 (:REWRITE NATP-RW))
 (248 165 (:REWRITE DEFAULT-<-2))
 (208 16 (:REWRITE ASSOCIATIVITY-OF-+))
 (169 165 (:REWRITE DEFAULT-<-1))
 (160 52 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (160 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (89 89 (:REWRITE RUN-ALWAYS-EXPANDS))
 (72 4 (:REWRITE LITTLE-BIG-INVERSE))
 (60 20 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (49 49 (:REWRITE STEPS-TO-CUTPOINT-IS-NATP))
 (46 6 (:REWRITE NATP-POSP))
 (42 6 (:REWRITE POSP-RW))
 (39 13 (:REWRITE FALSIFIER-IS-NATP-OR-OMEGA))
 (14 14 (:REWRITE NO-EXITPOINT-IMPLIES-NOT-EXITPOINT))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 )
