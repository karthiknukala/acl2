(NEGATE-TERM)
(PSEUDO-TERMP-OF-NEGATE-TERM
 (67 67 (:REWRITE DEFAULT-CAR))
 (64 64 (:REWRITE DEFAULT-CDR))
 (56 12 (:DEFINITION LEN))
 (26 26 (:TYPE-PRESCRIPTION LEN))
 (22 11 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (11 11 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(LOGIC-TERMP-OF-NEGATE-TERM
 (220 220 (:REWRITE DEFAULT-CAR))
 (217 217 (:REWRITE DEFAULT-CDR))
 (85 5 (:DEFINITION ARGLISTP))
 (72 36 (:REWRITE DEFAULT-+-2))
 (62 20 (:DEFINITION ASSOC-EQUAL))
 (45 5 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (40 5 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (36 36 (:REWRITE DEFAULT-+-1))
 (35 15 (:DEFINITION MEMBER-EQUAL))
 (35 5 (:DEFINITION ARGLISTP1))
 (30 5 (:DEFINITION ALL-VARS))
 (25 5 (:DEFINITION ALL-VARS1))
 (15 15 (:REWRITE DEFAULT-COERCE-2))
 (15 15 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (10 10 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION ARGLISTP1))
 (10 5 (:DEFINITION TRUE-LISTP))
 (10 5 (:DEFINITION ADD-TO-SET-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION LOGICP))
 (5 5 (:TYPE-PRESCRIPTION ARITY))
 )
