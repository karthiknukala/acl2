(DEFUNTYPEDLEMMANAME)
(DEFUNTYPEDFORMALS)
(DEFUNTYPEDFILTERTYPEDARGS)
(DEFUNTYPEDMEASURE (8 4
                      (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
                   (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(NAT-INDUCT (4 4
               (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(NAT-INDUCT-IS-BOOLEANP)
(NAT-INDUCT2)
(NAT-INDUCT2-IS-BOOLEANP)
(UPDATE-NTH-COLLAPSE (41 2 (:REWRITE NTH-WITH-LARGE-INDEX))
                     (32 1 (:DEFINITION NTH))
                     (20 4 (:DEFINITION LEN))
                     (9 7 (:REWRITE DEFAULT-<-2))
                     (9 5 (:REWRITE DEFAULT-+-2))
                     (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
                     (8 7 (:REWRITE DEFAULT-<-1))
                     (6 6 (:REWRITE DEFAULT-CDR))
                     (5 5 (:REWRITE DEFAULT-+-1))
                     (4 4
                        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                     (4 1 (:REWRITE <-+-NEGATIVE-0-1))
                     (2 2 (:LINEAR LEQ-POSITION-EQUAL-LEN))
                     (2 1 (:DEFINITION TRUE-LISTP))
                     (1 1 (:REWRITE ZP-OPEN))
                     (1 1 (:REWRITE DEFAULT-CAR)))
(LEN-MINUS-ONE (16 8 (:REWRITE DEFAULT-+-2))
               (11 11 (:REWRITE DEFAULT-CDR))
               (8 8 (:REWRITE DEFAULT-+-1))
               (3 3 (:LINEAR LEQ-POSITION-EQUAL-LEN))
               (2 1 (:REWRITE DEFAULT-<-2))
               (1 1 (:REWRITE DEFAULT-<-1))
               (1 1 (:META CANCEL_PLUS-LESSP-CORRECT)))
(CONSP-LEN-POSITIVE (7 4 (:REWRITE DEFAULT-+-2))
                    (6 6 (:LINEAR LEQ-POSITION-EQUAL-LEN))
                    (5 5 (:REWRITE DEFAULT-CDR))
                    (4 4 (:REWRITE DEFAULT-+-1))
                    (4 2 (:DEFINITION TRUE-LISTP))
                    (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(TRUE-LISTP-LEN-0-EQUAL-NIL (10 2 (:DEFINITION LEN))
                            (4 4 (:REWRITE DEFAULT-CDR))
                            (4 2 (:REWRITE DEFAULT-+-2))
                            (4 2 (:DEFINITION TRUE-LISTP))
                            (2 2 (:REWRITE DEFAULT-+-1))
                            (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
                            (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
                            (2 2 (:LINEAR LEQ-POSITION-EQUAL-LEN)))
(LIST-NAT-INDUCT (4 4
                    (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(LIST-NAT-INDUCT-IS-BOOLEANP)