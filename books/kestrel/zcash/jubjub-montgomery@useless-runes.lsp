(ZCASH::JUBJUB-MONTGOMERY-CURVE)
(ZCASH::MONTGOMERY-CURVEP-OF-JUBJUB-MONTGOMERY-CURVE)
(ZCASH::MOD-EXPT-FAST-LEMMA)
(ZCASH::MOD-EXPT-LEMMA)
(ZCASH::NOT-ZERO-LEMMA)
(ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB-MONTGOMERY-A-SQUARE-MINUS-4
 (9 1 (:DEFINITION EXPT))
 (6 6 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (6 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 3 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-MUL))
 (3 3 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (3 3 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (3 3 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (3 1 (:REWRITE DEFAULT-*-2))
 (2 1 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1 1 (:REWRITE DEFAULT-*-1))
 )