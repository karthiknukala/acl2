(NICE-OUTPUT-INDICATORP)
(SLOT-TO-PARAMETER-TYPE-ALIST-AUX)
(ALISTP-OF-SLOT-TO-PARAMETER-TYPE-ALIST-AUX
 (105 10 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (24 8 (:REWRITE JVM::ALISTP-WHEN-METHOD-PROGRAMP))
 (20 10 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION JVM::METHOD-PROGRAMP))
 (14 11 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (14 10 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (10 10 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 9 (:REWRITE DEFAULT-CAR))
 (9 3 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (8 8 (:REWRITE JVM::ALISTP-WHEN-JVM-INSTRUCTIONS-OKAYP))
 (7 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 2 (:REWRITE DEFAULT-+-2))
 (4 2 (:REWRITE DEFAULT-+-1))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION JVM::TYPE-SLOT-COUNT))
 (2 2 (:TYPE-PRESCRIPTION JVM::NATP-OF-TYPE-SLOT-COUNT))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SLOT-TO-PARAMETER-TYPE-ALIST-AUX
 (8 2 (:REWRITE JVM::TYPEP-OF-CAR))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SLOT-TO-PARAMETER-TYPE-ALIST)
(ALISTP-OF-SLOT-TO-PARAMETER-TYPE-ALIST)
(DESUGAR-NICE-OUTPUT-INDICATORP
 (679 74 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (208 58 (:REWRITE DEFAULT-CAR))
 (173 60 (:REWRITE DEFAULT-CDR))
 (99 99 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (91 47 (:REWRITE DEFAULT-<-2))
 (85 70 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (74 74 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (70 70 (:REWRITE CLR-DIFFERENTIAL))
 (54 54 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (48 47 (:REWRITE DEFAULT-<-1))
 (33 11 (:REWRITE JVM::ALISTP-WHEN-METHOD-PROGRAMP))
 (26 14 (:REWRITE DEFAULT-+-2))
 (24 8 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (22 22 (:TYPE-PRESCRIPTION JVM::METHOD-PROGRAMP))
 (16 16 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:REWRITE DEFAULT-+-1))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (11 11 (:REWRITE JVM::ALISTP-WHEN-JVM-INSTRUCTIONS-OKAYP))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (7 7 (:TYPE-PRESCRIPTION JVM::TYPEP))
 (7 7 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (2 1 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 )
