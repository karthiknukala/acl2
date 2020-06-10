(ADE::B-TO-F (12 12
                 (:TYPE-PRESCRIPTION TRUE-LISTP-SUBSEQ-TYPE-PRESCRIPTION)))
(ADE::FN-TO-MODULE-OUTS (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ADE::FN-TO-MODULE-BODY (1299 630 (:REWRITE DEFAULT-+-2))
                        (966 69 (:DEFINITION LENGTH))
                        (852 630 (:REWRITE DEFAULT-+-1))
                        (759 69 (:DEFINITION LEN))
                        (552 138 (:REWRITE COMMUTATIVITY-OF-+))
                        (552 138 (:DEFINITION INTEGER-ABS))
                        (216 171 (:REWRITE DEFAULT-<-2))
                        (207 207
                             (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                        (207 138 (:REWRITE STR::CONSP-OF-EXPLODE))
                        (195 171 (:REWRITE DEFAULT-<-1))
                        (138 138 (:REWRITE DEFAULT-UNARY-MINUS))
                        (138 69
                             (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                        (69 69
                            (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                        (69 69 (:REWRITE DEFAULT-REALPART))
                        (69 69 (:REWRITE DEFAULT-NUMERATOR))
                        (69 69 (:REWRITE DEFAULT-IMAGPART))
                        (69 69 (:REWRITE DEFAULT-DENOMINATOR))
                        (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ADE::FLATTEN-EXPR)
(ADE::FLATTEN-BINDING
     (1299 630 (:REWRITE DEFAULT-+-2))
     (966 69 (:DEFINITION LENGTH))
     (852 630 (:REWRITE DEFAULT-+-1))
     (759 69 (:DEFINITION LEN))
     (552 138 (:REWRITE COMMUTATIVITY-OF-+))
     (552 138 (:DEFINITION INTEGER-ABS))
     (216 171 (:REWRITE DEFAULT-<-2))
     (207 207
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (207 138 (:REWRITE STR::CONSP-OF-EXPLODE))
     (195 171 (:REWRITE DEFAULT-<-1))
     (138 138 (:REWRITE DEFAULT-UNARY-MINUS))
     (138 69
          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (69 69 (:TYPE-PRESCRIPTION LEN))
     (69 69
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (69 69 (:REWRITE DEFAULT-REALPART))
     (69 69 (:REWRITE DEFAULT-NUMERATOR))
     (69 69 (:REWRITE DEFAULT-IMAGPART))
     (69 69 (:REWRITE DEFAULT-DENOMINATOR))
     (22 22
         (:TYPE-PRESCRIPTION TRUE-LISTP-SUBSEQ-TYPE-PRESCRIPTION))
     (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ADE::ADD-PREFIX-TO-NAME)
(ADE::ADD-PREFIX-TO-NAMES (2 2 (:REWRITE DEFAULT-CAR))
                          (1 1 (:REWRITE DEFAULT-CDR)))
(ADE::ADD-PREFIX-TO-STATE-NAMES (7 7 (:REWRITE DEFAULT-CAR))
                                (1 1 (:REWRITE DEFAULT-CDR)))
(ADE::DEFINE-CONTROL-STATES
     (68 16
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (46 38 (:REWRITE DEFAULT-CAR))
     (26 13
         (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (22 14 (:REWRITE DEFAULT-CDR))
     (16 4
         (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (9 9 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (8 8
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (8 8 (:REWRITE DEFAULT-SYMBOL-NAME))
     (8 4
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (6 6
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)))
(ADE::DEFINE-CONTROL-VECTOR-ACCESSORS)
(ADE::CONTROL-LET)
(ADE::BUILD-ST)
(ADE::CV-LEMMA-CONCL)
(ADE::UPDATE-TEMPLATE)
(ADE::ADD-PREFIX-AND-SUFFIX-TO-NAME (3 3 (:REWRITE DEFAULT-CDR))
                                    (3 3 (:REWRITE DEFAULT-CAR))
                                    (2 2 (:REWRITE DEFAULT-SYMBOL-NAME)))
(ADE::ADD-PREFIX-AND-SUFFIX-TO-STATE-NAMES (7 7 (:REWRITE DEFAULT-CAR))
                                           (1 1 (:REWRITE DEFAULT-CDR)))
(ADE::DEFINE-CONTROL-VECTOR-FUNCTIONS)
(ADE::BIND-VALUES)
(ADE::WIRE-OCCS)
(ADE::B-AND-EXPR (1 1 (:TYPE-PRESCRIPTION ADE::B-AND-EXPR)))
(ADE::UNWIND (617 291 (:REWRITE DEFAULT-+-2))
             (420 30 (:DEFINITION LENGTH))
             (388 291 (:REWRITE DEFAULT-+-1))
             (330 30 (:DEFINITION LEN))
             (240 60 (:REWRITE COMMUTATIVITY-OF-+))
             (240 60 (:DEFINITION INTEGER-ABS))
             (95 73 (:REWRITE DEFAULT-<-2))
             (90 90
                 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
             (90 60 (:REWRITE STR::CONSP-OF-EXPLODE))
             (81 73 (:REWRITE DEFAULT-<-1))
             (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
             (60 30
                 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
             (30 30 (:TYPE-PRESCRIPTION LEN))
             (30 30
                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
             (30 30 (:REWRITE DEFAULT-REALPART))
             (30 30 (:REWRITE DEFAULT-NUMERATOR))
             (30 30 (:REWRITE DEFAULT-IMAGPART))
             (30 30 (:REWRITE DEFAULT-DENOMINATOR))
             (2 2 (:TYPE-PRESCRIPTION ADE::B-AND-EXPR))
             (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ADE::UNWIND-NEXT-ST)
(ADE::COLLECT-FROM-ALIST (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ADE::COMPUTE-NEXT-ST)
(ADE::DEFINE-NEXT-STATE)
(ADE::WIRE-OCCS-FROM-DECODED-STATE (2 2 (:REWRITE DEFAULT-CAR))
                                   (2 2 (:REWRITE DEFAULT-<-2))
                                   (2 2 (:REWRITE DEFAULT-<-1))
                                   (1 1 (:REWRITE DEFAULT-CDR)))
(ADE::TRANSLATE-B-FNS (1029 508 (:REWRITE DEFAULT-+-2))
                      (784 56 (:DEFINITION LENGTH))
                      (672 508 (:REWRITE DEFAULT-+-1))
                      (616 56 (:DEFINITION LEN))
                      (448 112 (:REWRITE COMMUTATIVITY-OF-+))
                      (448 112 (:DEFINITION INTEGER-ABS))
                      (175 139 (:REWRITE DEFAULT-<-2))
                      (168 168
                           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                      (168 112 (:REWRITE STR::CONSP-OF-EXPLODE))
                      (159 139 (:REWRITE DEFAULT-<-1))
                      (112 112 (:REWRITE DEFAULT-UNARY-MINUS))
                      (112 56
                           (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                      (56 56 (:TYPE-PRESCRIPTION LEN))
                      (56 56
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                      (56 56 (:REWRITE DEFAULT-REALPART))
                      (56 56 (:REWRITE DEFAULT-NUMERATOR))
                      (56 56 (:REWRITE DEFAULT-IMAGPART))
                      (56 56 (:REWRITE DEFAULT-DENOMINATOR)))
(ADE::MAKE-IF-TREE (615 287 (:REWRITE DEFAULT-+-2))
                   (420 30 (:DEFINITION LENGTH))
                   (390 287 (:REWRITE DEFAULT-+-1))
                   (330 30 (:DEFINITION LEN))
                   (240 60 (:REWRITE COMMUTATIVITY-OF-+))
                   (240 60 (:DEFINITION INTEGER-ABS))
                   (95 73 (:REWRITE DEFAULT-<-2))
                   (90 90
                       (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                   (90 60 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (81 73 (:REWRITE DEFAULT-<-1))
                   (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
                   (60 30
                       (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                   (30 30 (:TYPE-PRESCRIPTION LEN))
                   (30 30
                       (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (30 30 (:REWRITE DEFAULT-REALPART))
                   (30 30 (:REWRITE DEFAULT-NUMERATOR))
                   (30 30 (:REWRITE DEFAULT-IMAGPART))
                   (30 30 (:REWRITE DEFAULT-DENOMINATOR)))
(ADE::NEXT-CNTL-STATE-LEMMAS)
(ADE::GENERATE-NEXT-CNTL-STATE-LEMMAS)
(ADE::BIND-SIGNALS-TO-VAL)
(ADE::MODULE$STATE-INTERLEAVINGS-GEN-FN)
(ADE::IDX->CAR-CDR)
(ADE::GO-GEN1)
(ADE::REMOVE-LST-LST (2 2 (:REWRITE DEFAULT-CDR))
                     (2 2 (:REWRITE DEFAULT-CAR))
                     (2 1 (:DEFINITION TRUE-LISTP))
                     (1 1 (:TYPE-PRESCRIPTION ADE::REMOVE-LST)))
(ADE::REMOVE-LEN-<-2)
(ADE::GO-GEN (288 282 (:REWRITE DEFAULT-CDR))
             (256 250 (:REWRITE DEFAULT-CAR))
             (242 46 (:DEFINITION LEN))
             (175 35 (:DEFINITION REMOVE-EQUAL))
             (160 4 (:REWRITE LEN-WHEN-PREFIXP))
             (124 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
             (98 52 (:REWRITE DEFAULT-+-2))
             (80 40 (:DEFINITION TRUE-LISTP))
             (77 47 (:REWRITE DEFAULT-<-1))
             (52 52 (:REWRITE DEFAULT-+-1))
             (51 47 (:REWRITE DEFAULT-<-2))
             (28 28 (:LINEAR LEN-WHEN-PREFIXP))
             (16 4 (:DEFINITION ADE::IDX->CAR-CDR))
             (14 14
                 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
             (8 8 (:TYPE-PRESCRIPTION PREFIXP))
             (4 4 (:REWRITE ZP-OPEN))
             (4 4
                (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
             (4 4
                (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
             (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
             (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
             (4 4
                (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
             (4 4
                (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(ADE::ST-TRANS-GEN
     (1228 56 (:DEFINITION BINARY-APPEND))
     (608 172 (:REWRITE STR::CONSP-OF-EXPLODE))
     (570 152 (:REWRITE DEFAULT-CDR))
     (568 150 (:REWRITE DEFAULT-CAR))
     (346 97
          (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (168 1 (:DEFINITION ADE::GO-GEN))
     (140 140 (:REWRITE STR::NATSTR-NONEMPTY))
     (128 67
          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (95 95 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (40 14
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (40 1 (:REWRITE LEN-WHEN-PREFIXP))
     (31 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (30 6 (:DEFINITION LEN))
     (20 20 (:TYPE-PRESCRIPTION ADE::GO-GEN1))
     (17 1 (:DEFINITION ADE::REMOVE-LEN-<-2))
     (16 8 (:REWRITE STR::DIGIT-LISTP-OF-APPEND))
     (16 2 (:DEFINITION ADE::REMOVE-LST))
     (13 7 (:REWRITE DEFAULT-+-2))
     (12 4 (:DEFINITION ADE::GO-GEN1))
     (11 11 (:REWRITE DEFAULT-SYMBOL-NAME))
     (11 11
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (11 1 (:DEFINITION ADE::REMOVE-LST-LST))
     (10 2 (:DEFINITION REMOVE-EQUAL))
     (8 2
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (6 4 (:REWRITE DEFAULT-<-1))
     (6 3 (:DEFINITION TRUE-LISTP))
     (5 4 (:REWRITE DEFAULT-<-2))
     (4 4
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (4 4 (:DEFINITION ADE::IDX->CAR-CDR))
     (4 2
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (3 3
        (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (2 2
        (:TYPE-PRESCRIPTION ADE::REMOVE-LST-LST))
     (2 2 (:TYPE-PRESCRIPTION ADE::REMOVE-LST))
     (2 2 (:TYPE-PRESCRIPTION PREFIXP))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(ADE::ST-TRANS-LST (3 3 (:REWRITE DEFAULT-CDR))
                   (3 3 (:REWRITE DEFAULT-CAR))
                   (3 3 (:REWRITE DEFAULT-+-2))
                   (3 3 (:REWRITE DEFAULT-+-1))
                   (1 1 (:REWRITE ZP-OPEN))
                   (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
                   (1 1 (:REWRITE DEFAULT-<-2))
                   (1 1 (:REWRITE DEFAULT-<-1)))
(ADE::ST-TRANS->NUMSTEPS-LST
     (585 25 (:DEFINITION BINARY-APPEND))
     (298 82 (:REWRITE STR::CONSP-OF-EXPLODE))
     (257 56 (:REWRITE DEFAULT-CDR))
     (257 56 (:REWRITE DEFAULT-CAR))
     (154 39
          (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (70 70 (:REWRITE STR::NATSTR-NONEMPTY))
     (50 26
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (38 38 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (33 33 (:REWRITE DEFAULT-+-2))
     (33 33 (:REWRITE DEFAULT-+-1))
     (18 6
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (8 4 (:REWRITE STR::DIGIT-LISTP-OF-APPEND))
     (6 6 (:REWRITE DEFAULT-SYMBOL-NAME))
     (4 4
        (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(ADE::ST-TRANS-FN
     (1996 1
           (:DEFINITION ADE::ST-TRANS->NUMSTEPS-LST))
     (1565 30 (:DEFINITION CHARACTER-LISTP))
     (943 49 (:DEFINITION BINARY-APPEND))
     (439 168 (:REWRITE DEFAULT-CDR))
     (423 71
          (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (401 130 (:REWRITE DEFAULT-CAR))
     (390 148 (:REWRITE STR::CONSP-OF-EXPLODE))
     (303 1 (:DEFINITION ADE::ST-TRANS-GEN))
     (210 42 (:DEFINITION LEN))
     (202 63
          (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (173 173
          (:TYPE-PRESCRIPTION STR::STRINGP-OF-NATSTR))
     (164 1 (:DEFINITION ADE::GO-GEN))
     (121 79 (:REWRITE DEFAULT-+-2))
     (101 59
          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (79 79 (:REWRITE DEFAULT-+-1))
     (77 77
         (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (70 70 (:REWRITE STR::NATSTR-NONEMPTY))
     (57 57 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (46 32
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (40 1 (:REWRITE LEN-WHEN-PREFIXP))
     (37 37 (:REWRITE DEFAULT-SYMBOL-NAME))
     (31 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (20 20 (:TYPE-PRESCRIPTION ADE::GO-GEN1))
     (20 5
         (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (18 18
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (17 1 (:DEFINITION ADE::REMOVE-LEN-<-2))
     (16 2 (:DEFINITION ADE::REMOVE-LST))
     (12 4 (:DEFINITION ADE::GO-GEN1))
     (12 2 (:REWRITE CHARACTER-LISTP-APPEND))
     (11 1 (:DEFINITION ADE::REMOVE-LST-LST))
     (10 10
         (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (10 5
         (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (10 2 (:DEFINITION REMOVE-EQUAL))
     (8 8 (:REWRITE STR::DIGIT-LISTP-OF-NATSTR))
     (8 4 (:REWRITE STR::DIGIT-LISTP-OF-APPEND))
     (8 1 (:REWRITE ZP-OPEN))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (5 3 (:REWRITE DEFAULT-<-2))
     (5 3 (:REWRITE DEFAULT-<-1))
     (4 2 (:DEFINITION TRUE-LISTP))
     (4 1 (:REWRITE REV-WHEN-NOT-CONSP))
     (3 3
        (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (3 1 (:REWRITE APPEND-OF-NIL))
     (2 2
        (:TYPE-PRESCRIPTION ADE::REMOVE-LST-LST))
     (2 2 (:TYPE-PRESCRIPTION ADE::REMOVE-LST))
     (2 2 (:TYPE-PRESCRIPTION PREFIXP))
     (2 1 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (2 1 (:REWRITE STR::IMPLODE-OF-EXPLODE))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))