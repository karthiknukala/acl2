(MZERO
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ZERO-BOOTSTRAP
 (36 36 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (31 19 (:REWRITE DEFAULT-+-2))
 (30 10 (:DEFINITION VZERO))
 (25 3 (:REWRITE COL-CDR-EMPTY))
 (19 19 (:REWRITE DEFAULT-+-1))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (3 3 (:TYPE-PRESCRIPTION COL-CDR))
 )
(MZERO
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (11 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 3 (:DEFINITION VZERO))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(MATRIXP-ZERO)
(M-EMPTY-ZERO
 (15 5 (:DEFINITION VZERO))
 (13 13 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (9 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(COL-COUNT-ZERO
 (8 1 (:DEFINITION MZERO))
 (6 6 (:REWRITE ZP-OPEN))
 (3 1 (:DEFINITION VZERO))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ROW-COUNT-ZERO
 (108 4 (:REWRITE ROW-CDR-EMPTY))
 (44 44 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (31 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 5 (:DEFINITION VZERO))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(ZERO-BY-COL-DEF
 (176 10 (:REWRITE COL-CONS-ROW-CONS-UNIT))
 (133 103 (:REWRITE DEFAULT-+-2))
 (103 103 (:REWRITE DEFAULT-+-1))
 (90 30 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (20 20 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (20 20 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (14 7 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE EQUAL-CONSTANT-+))
 (2 1 (:REWRITE DEFAULT-CAR))
 )
