(MEASURE)
(SIGMA)
(B)
(QP)
(WP)
(R)
(LOOP-INVARIANT-WP-DEF-1)
(LOOP-INVARIANT-WP-DEF-2)
(LOOP-INVARIANT-ORDINALP
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LOOP-INVARIANT-ORD-<
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(LOOP-INVARIANT-R-1)
(LOOP-INVARIANT-R-2)
(WP-IND)
(WP-IS-WEAKEST-INVARIANT)
(MEASURE-G)
(TAU)
(QT)
(RHO)
(RHOH)
(BB)
(G)
(ID)
(OP)
(H)
(RT)
(HS)
(TAIL-RECURSION-G-DEF-1)
(TAIL-RECURSION-G-DEF-2)
(TAIL-RECURSION-ORDINALP
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TAIL-RECURSION-ORD-<
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ZP-OPEN))
 )
(TAIL-RECURSION-H-DEF-1)
(TAIL-RECURSION-H-DEF-2)
(TAIL-RECURSION-RT
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TAIL-RECURSION-HS-1
 (1 1 (:REWRITE ZP-OPEN))
 )
(TAIL-RECURSION-HS-2
 (12 2 (:REWRITE TAIL-RECURSION-HS-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TAIL-RECURSION-OP-RHO-RHOH
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TAIL-RECURSION-OP-ID
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(A-G)
(A-G-AS-OP-H)
(G-AS-A-G)
(G=H)
(FN1)
(FN2)
(B1)
(B2)
(Q1)
(Q2)
(P)
(MEASURE1)
(SIGMA1)
(SIGMA2)
(ID-ALT)
(ALTERNATIVE-INDUCTION-FN1-DEF-1)
(ALTERNATIVE-INDUCTION-FN1-DEF-2)
(ALTERNATIVE-INDUCTION-FN2-DEF-1)
(ALTERNATIVE-INDUCTION-FN2-DEF-2)
(ALTERNATIVE-INDUCTION-ORDINALP
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ALTERNATIVE-INDUCTION-ORD-<
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(ALTERNATIVE-INDUCTION-ID-ALT
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ALTERNATIVE-INDUCTION-B2-ID-ALT
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ALTERNATIVE-INDUCTION-P)
(ALTERNATIVE-INDUCTION-Q2-ID-ALT)
(FN1-IND)
(FN1-AS-FN2)
(MAKE-SUBS)
(SET-TO-PREDICATE)
(MAKE-B)
(MAKE-SIGMA)
(BUILD-INSTANCE)
