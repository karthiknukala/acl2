(DM::CHOOSE)
(DM::BINOMIAL-EXPANSION
 (14 13 (:REWRITE DEFAULT-+-2))
 (14 13 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(DM::SUM-LIST)
(DM::FACTORIAL-REWRITE
 (24 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(DM::CHOOSE-REWRITE
 (50 6 (:DEFINITION DM::FACT))
 (24 24 (:TYPE-PRESCRIPTION DM::FACT))
 (22 10 (:REWRITE DEFAULT-*-2))
 (14 10 (:REWRITE DEFAULT-*-1))
 (12 6 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 2 (:REWRITE DEFAULT-UNARY-/))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:DEFINITION NOT))
 )
(DM::BINOMIAL-EXPANSION-REWRITE
 (192 4 (:DEFINITION EXPT))
 (126 12 (:DEFINITION N-EXPT))
 (94 32 (:REWRITE DEFAULT-*-2))
 (60 32 (:REWRITE DEFAULT-*-1))
 (56 51 (:REWRITE DEFAULT-<-1))
 (55 51 (:REWRITE DEFAULT-<-2))
 (48 48 (:REWRITE DEFAULT-+-2))
 (48 48 (:REWRITE DEFAULT-+-1))
 (37 37 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (32 32 (:TYPE-PRESCRIPTION N-EXPT))
 (26 18 (:REWRITE FOLD-CONSTS-IN-+))
 (16 4 (:REWRITE DEFAULT-UNARY-/))
 (12 12 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (12 12 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (12 12 (:TYPE-PRESCRIPTION EXPT))
 (8 4 (:DEFINITION FIX))
 (6 6 (:TYPE-PRESCRIPTION DM::CHOOSE))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZIP-OPEN))
 )
(DM::SUMLIST-REWRITE
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(DM::BINOMIAL-THEOREM
 (12 12 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 )
