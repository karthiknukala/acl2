(MAKE-AXE-RULE-SAFE
 (295 5 (:DEFINITION PSEUDO-TERMP))
 (81 9 (:DEFINITION LENGTH))
 (66 12 (:DEFINITION LEN))
 (62 62 (:REWRITE DEFAULT-CDR))
 (57 57 (:REWRITE DEFAULT-CAR))
 (34 17 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
 (30 3 (:DEFINITION SYMBOL-LISTP))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (24 12 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (22 8 (:DEFINITION TRUE-LISTP))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (18 9 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (17 17 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 15 (:REWRITE SYMBOLP-WHEN-MEMBERP))
 (15 3 (:REWRITE PSEUDO-TERMP-OF-CADDR))
 (12 12 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(LHS-AND-RHS-OF-SIMPLE-RULE)