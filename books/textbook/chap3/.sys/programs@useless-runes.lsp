(FIB
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(PASCAL
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(MEM)
(SUBSET)
(UN)
(INT)
(DIFF)
(REV)
(INSERT)
(ISORT)
(FLATTEN
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SWAP-TREE)
(DEPTH)
(SUBTREE)
(REPLACE-SUBTREE)
(DEEP-TIP-1)
(DEEP-TIP-AUX)
(DEEP-TIP)
