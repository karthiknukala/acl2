(AIGNET::ID-IS-XOR
 (12158 30 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (7248 80 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (5364 3963 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (5312 128 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2976 96 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT))
 (2433 129 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (1600 176 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (1457 449 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1120 128 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (896 176 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (896 176 (:REWRITE DEFAULT-CDR))
 (798 30 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (736 80 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (656 80 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (576 80 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (480 96 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (477 477 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (477 477 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (477 477 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (477 477 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (395 83 (:REWRITE DEFAULT-CAR))
 (355 58 (:REWRITE AIGNET::STYPE-BY-CTYPE))
 (342 342 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (342 342 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (320 64 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (224 160 (:REWRITE NFIX-WHEN-NOT-NATP))
 (224 160 (:REWRITE NFIX-WHEN-NATP))
 (197 100 (:REWRITE DEFAULT-<-1))
 (160 160 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (129 129 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (102 100 (:REWRITE DEFAULT-<-2))
 (97 97 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (80 80 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (80 80 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (33 5 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (16 16 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (16 16 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (5 5 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (5 5 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE-QUOTED-CONSTANT AIGNET::STYPE-FIX-UNDER-STYPE-EQUIV))
 (2 2 (:REWRITE AIGNET::STYPE-COUNT-OF-ATOM))
 (2 2 (:LINEAR AIGNET::STYPE-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (2 2 (:LINEAR AIGNET::STYPE-COUNT-WHEN-AIGNET-EXTENSION))
 (2 2 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-STYPE-COUNT-GTE))
 (1 1 (:REWRITE AIGNET::NODE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE AIGNET::AIGNET-NODES-OK-OF-SUFFIX-INVERSE))
 (1 1 (:REWRITE AIGNET::AIGNET-NODES-OK-OF-EXTENSION))
 )
(AIGNET::LITP-OF-ID-IS-XOR.CHILD1
 (5764 4 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (3644 20 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (2912 32 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2400 1038 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (1320 24 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT))
 (1288 36 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (1038 1038 (:TYPE-PRESCRIPTION AIGNET::NODE-LISTP))
 (1038 1038 (:TYPE-PRESCRIPTION AIGNET::LOOKUP-ID))
 (772 112 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (664 44 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (488 44 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (488 44 (:REWRITE DEFAULT-CDR))
 (480 480 (:TYPE-PRESCRIPTION SATLINK::VARP-OF-LIT->VAR))
 (472 32 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (456 24 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (336 24 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (304 20 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (284 20 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (264 24 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (264 20 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (252 252 (:TYPE-PRESCRIPTION AIGNET::FANIN-COUNT))
 (200 40 (:REWRITE NFIX-WHEN-NATP))
 (196 4 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (152 40 (:REWRITE NFIX-WHEN-NOT-NATP))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (132 132 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (128 128 (:TYPE-PRESCRIPTION NFIX))
 (96 96 (:TYPE-PRESCRIPTION NATP))
 (96 48 (:REWRITE NATP-WHEN-GTE-0))
 (92 92 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (80 16 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (72 48 (:REWRITE DEFAULT-<-2))
 (72 48 (:REWRITE DEFAULT-<-1))
 (72 6 (:REWRITE DEFAULT-CAR))
 (66 66 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (66 66 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (48 48 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (48 48 (:REWRITE NATP-WHEN-INTEGERP))
 (40 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (39 6 (:REWRITE AIGNET::STYPE-BY-CTYPE))
 (36 36 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (32 32 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (28 28 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (24 24 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (24 24 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (24 24 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (24 24 (:LINEAR LISTPOS-COMPLETE))
 (20 20 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (20 20 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (4 4 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (4 4 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::LITP-OF-ID-IS-XOR.CHILD2
 (5764 4 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (3644 20 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (2912 32 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2400 1038 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (1320 24 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT))
 (1288 36 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (1038 1038 (:TYPE-PRESCRIPTION AIGNET::NODE-LISTP))
 (1038 1038 (:TYPE-PRESCRIPTION AIGNET::LOOKUP-ID))
 (772 112 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (664 44 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (488 44 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (488 44 (:REWRITE DEFAULT-CDR))
 (480 480 (:TYPE-PRESCRIPTION SATLINK::VARP-OF-LIT->VAR))
 (472 32 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (456 24 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (336 24 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (304 20 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (284 20 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (264 24 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (264 20 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (252 252 (:TYPE-PRESCRIPTION AIGNET::FANIN-COUNT))
 (200 40 (:REWRITE NFIX-WHEN-NATP))
 (196 4 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (152 40 (:REWRITE NFIX-WHEN-NOT-NATP))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (132 132 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (132 132 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (128 128 (:TYPE-PRESCRIPTION NFIX))
 (96 96 (:TYPE-PRESCRIPTION NATP))
 (96 48 (:REWRITE NATP-WHEN-GTE-0))
 (92 92 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (80 16 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (72 48 (:REWRITE DEFAULT-<-2))
 (72 48 (:REWRITE DEFAULT-<-1))
 (72 6 (:REWRITE DEFAULT-CAR))
 (66 66 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (66 66 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (48 48 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (48 48 (:REWRITE NATP-WHEN-INTEGERP))
 (40 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (39 6 (:REWRITE AIGNET::STYPE-BY-CTYPE))
 (36 36 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (32 32 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (28 28 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (24 24 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (24 24 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (24 24 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (24 24 (:LINEAR LISTPOS-COMPLETE))
 (20 20 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (20 20 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (4 4 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (4 4 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::AIGNET-LITP-OF-ID-IS-XOR
 (16846 14 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (7896 104 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2542 364 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1516 142 (:REWRITE DEFAULT-CDR))
 (1508 134 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (1292 68 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (952 68 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (952 62 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (890 62 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (828 62 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (686 14 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (471 471 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (471 471 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (471 471 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (471 471 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (460 132 (:REWRITE NFIX-WHEN-NOT-NATP))
 (307 37 (:REWRITE DEFAULT-CAR))
 (272 136 (:REWRITE NATP-WHEN-GTE-0))
 (268 268 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (268 268 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (236 152 (:REWRITE DEFAULT-<-2))
 (228 152 (:REWRITE DEFAULT-<-1))
 (136 136 (:REWRITE NATP-WHEN-INTEGERP))
 (124 124 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (123 123 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (103 103 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (88 88 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (85 85 (:LINEAR LISTPOS-COMPLETE))
 (74 74 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (74 74 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (74 74 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (68 68 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (68 68 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (62 62 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (62 62 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (14 14 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (14 14 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(AIGNET::ID-EVAL-WHEN-ID-IS-XOR
 (19144 112 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (5488 112 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (3647 307 (:REWRITE BFIX-WHEN-NOT-1))
 (3184 48 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2930 650 (:REWRITE DEFAULT-CAR))
 (2806 2806 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (2806 2806 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (1633 1633 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (1633 1633 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (1633 1633 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (1633 1633 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (1420 664 (:REWRITE DEFAULT-CDR))
 (1372 328 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1214 1214 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1204 1204 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1204 1204 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (928 800 (:REWRITE NFIX-WHEN-NOT-NATP))
 (867 307 (:REWRITE BFIX-WHEN-NOT-BITP))
 (696 60 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (674 674 (:REWRITE DEFAULT-+-2))
 (674 674 (:REWRITE DEFAULT-+-1))
 (614 614 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (614 307 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (614 307 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (470 10 (:DEFINITION GET-BIT))
 (460 10 (:DEFINITION BITS$AI))
 (456 24 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (440 10 (:DEFINITION AIGNET::CI-ID->IONUM))
 (320 10 (:DEFINITION NTH))
 (281 281 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (273 273 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (229 229 (:LINEAR LISTPOS-COMPLETE))
 (216 216 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (191 191 (:REWRITE AIGNET::LIT-EVAL-PRESERVED-BY-EXTENSION-INVERSE))
 (191 191 (:REWRITE AIGNET::LIT-EVAL-PRESERVED-BY-EXTENSION))
 (150 10 (:REWRITE ZP-WHEN-GT-0))
 (144 84 (:REWRITE DEFAULT-<-2))
 (130 10 (:REWRITE AIGNET::STYPE-COUNT-OF-ATOM))
 (124 84 (:REWRITE DEFAULT-<-1))
 (120 120 (:TYPE-PRESCRIPTION AIGNET::NATP-OF-STYPE-COUNT))
 (112 112 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (112 112 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 (108 108 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (96 48 (:REWRITE NATP-WHEN-GTE-0))
 (85 85 (:TYPE-PRESCRIPTION AIGNET::RETURN-TYPE-OF-EVAL-XOR-OF-LITS.VAL))
 (80 10 (:REWRITE ZP-WHEN-INTEGERP))
 (75 5 (:REWRITE BFIX-BITP))
 (70 70 (:TYPE-PRESCRIPTION BITP))
 (55 5 (:REWRITE BFIX-EQUAL-0))
 (48 48 (:REWRITE NATP-WHEN-INTEGERP))
 (35 35 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (26 26 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (25 5 (:DEFINITION BIT->BOOL$INLINE))
 (24 24 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (20 10 (:LINEAR AIGNET::STYPE-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (20 10 (:LINEAR AIGNET::STYPE-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (10 10 (:REWRITE NTH-WHEN-PREFIXP))
 (10 10 (:REWRITE BFIX-UNDER-BIT-EQUIV))
 (10 10 (:LINEAR AIGNET::STYPE-COUNT-WHEN-AIGNET-EXTENSION))
 (10 10 (:LINEAR AIGNET::STYPE-COUNT-CDR-WHEN-AIGNET-EXTENSION-P))
 (10 10 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-STYPE-COUNT-GTE))
 (6 6 (:REWRITE AIGNET::EVAL-AND-PRESERVED-BY-EXTENSION-INVERSE))
 (6 6 (:REWRITE AIGNET::EVAL-AND-OF-LITS-PRESERVED-BY-EXTENSION))
 (5 5 (:TYPE-PRESCRIPTION BFIX$INLINE))
 (3 3 (:REWRITE AIGNET::ID-EVAL-PRESERVED-BY-EXTENSION-INVERSE))
 (3 3 (:REWRITE AIGNET::ID-EVAL-PRESERVED-BY-EXTENSION))
 (1 1 (:REWRITE AIGNET::EVAL-XOR-PRESERVED-BY-EXTENSION-INVERSE))
 (1 1 (:REWRITE AIGNET::EVAL-XOR-OF-LITS-PRESERVED-BY-EXTENSION))
 )
(AIGNET::ID-IS-XOR-NOT-XOR-IMPLIES-AND
 (14410 10 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (7624 88 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (2102 308 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1772 118 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (1300 118 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (1300 118 (:REWRITE DEFAULT-CDR))
 (1292 88 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (1292 68 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (952 68 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (816 54 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (762 54 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (708 54 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (700 64 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (556 108 (:REWRITE NFIX-WHEN-NATP))
 (505 49 (:REWRITE DEFAULT-CAR))
 (490 10 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (420 108 (:REWRITE NFIX-WHEN-NOT-NATP))
 (413 413 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (413 413 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (413 413 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (413 413 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (272 272 (:TYPE-PRESCRIPTION NATP))
 (272 136 (:REWRITE NATP-WHEN-GTE-0))
 (204 136 (:REWRITE DEFAULT-<-2))
 (196 136 (:REWRITE DEFAULT-<-1))
 (176 176 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (176 176 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (136 136 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (136 136 (:REWRITE NATP-WHEN-INTEGERP))
 (108 108 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (102 102 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (82 82 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (72 72 (:LINEAR LISTPOS-COMPLETE))
 (68 68 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (68 68 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (68 68 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (54 54 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (54 54 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (36 36 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (36 36 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (36 36 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (10 10 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (10 10 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::LIT-ID-BOUND-OF-ID-IS-XOR-CHILD1
 (8386 12 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (4508 28 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (3184 48 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (1895 63 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (1212 168 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (721 85 (:REWRITE DEFAULT-CDR))
 (696 60 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (588 12 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (456 24 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (440 28 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (412 28 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (384 28 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (336 24 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (259 259 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (257 50 (:REWRITE DEFAULT-CAR))
 (255 255 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (255 255 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (227 87 (:REWRITE NFIX-WHEN-NOT-NATP))
 (132 132 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (119 73 (:REWRITE DEFAULT-<-1))
 (116 73 (:REWRITE DEFAULT-<-2))
 (108 54 (:REWRITE NATP-WHEN-GTE-0))
 (77 77 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (77 77 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (77 77 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (63 63 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (56 56 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (55 55 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (54 54 (:REWRITE NATP-WHEN-INTEGERP))
 (51 51 (:LINEAR LISTPOS-COMPLETE))
 (48 48 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (48 48 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (28 28 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (28 28 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (27 27 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (25 25 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (24 24 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (12 12 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (12 12 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::LIT-ID-BOUND-OF-ID-IS-XOR-CHILD2
 (8386 12 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (4508 28 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (3184 48 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (1895 63 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (1212 168 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (721 85 (:REWRITE DEFAULT-CDR))
 (696 60 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (588 12 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (456 24 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (440 28 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (412 28 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (384 28 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (336 24 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (259 259 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (259 259 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (257 50 (:REWRITE DEFAULT-CAR))
 (255 255 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (255 255 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (227 87 (:REWRITE NFIX-WHEN-NOT-NATP))
 (132 132 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (119 73 (:REWRITE DEFAULT-<-1))
 (116 73 (:REWRITE DEFAULT-<-2))
 (108 54 (:REWRITE NATP-WHEN-GTE-0))
 (77 77 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (77 77 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (77 77 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (63 63 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (56 56 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (55 55 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (54 54 (:REWRITE NATP-WHEN-INTEGERP))
 (51 51 (:LINEAR LISTPOS-COMPLETE))
 (48 48 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (48 48 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (28 28 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (28 28 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (27 27 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (25 25 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (24 24 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (12 12 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (12 12 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::ID-IS-XOR-OF-NFIX-ID
 (11528 8 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (7288 40 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (5824 64 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (4794 2073 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (2640 48 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT))
 (2576 72 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (2073 2073 (:TYPE-PRESCRIPTION AIGNET::NODE-LISTP))
 (2073 2073 (:TYPE-PRESCRIPTION AIGNET::LOOKUP-ID))
 (1544 224 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1328 88 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (976 88 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (976 88 (:REWRITE DEFAULT-CDR))
 (960 960 (:TYPE-PRESCRIPTION SATLINK::VARP-OF-LIT->VAR))
 (944 64 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (912 48 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (672 48 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (608 40 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (568 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (528 48 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (528 40 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (407 81 (:REWRITE NFIX-WHEN-NATP))
 (392 8 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (309 81 (:REWRITE NFIX-WHEN-NOT-NATP))
 (268 268 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (268 268 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (268 268 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (268 268 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (196 196 (:TYPE-PRESCRIPTION NATP))
 (196 98 (:REWRITE NATP-WHEN-GTE-0))
 (184 184 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (160 32 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (145 97 (:REWRITE DEFAULT-<-2))
 (145 97 (:REWRITE DEFAULT-<-1))
 (135 12 (:REWRITE DEFAULT-CAR))
 (132 132 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (132 132 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (98 98 (:REWRITE NATP-WHEN-INTEGERP))
 (96 96 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (80 80 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (72 72 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (67 12 (:REWRITE AIGNET::STYPE-BY-CTYPE))
 (64 64 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (56 56 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (48 48 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (48 48 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (48 48 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (48 48 (:LINEAR LISTPOS-COMPLETE))
 (40 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (40 40 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (12 12 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (12 12 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (12 12 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (8 8 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (8 8 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 )
(AIGNET::ID-IS-XOR-NAT-EQUIV-CONGRUENCE-ON-ID)
(AIGNET::ID-IS-XOR-OF-NODE-LIST-FIX-AIGNET
 (11528 8 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-VARS-MISMATCH))
 (7288 40 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-WEAK))
 (5824 64 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID))
 (4794 2073 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (2640 48 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT))
 (2576 72 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION-BIND-INVERSE))
 (2075 2075 (:TYPE-PRESCRIPTION AIGNET::NODE-LISTP))
 (2073 2073 (:TYPE-PRESCRIPTION AIGNET::LOOKUP-ID))
 (1544 224 (:REWRITE AIGNET::FANIN-COUNT-OF-ATOM))
 (1328 88 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-ID))
 (976 88 (:REWRITE AIGNET::FANIN-COUNT-OF-CDR-STRONG))
 (976 88 (:REWRITE DEFAULT-CDR))
 (960 960 (:TYPE-PRESCRIPTION SATLINK::VARP-OF-LIT->VAR))
 (944 64 (:REWRITE AIGNET::FANIN-COUNT-OF-LOOKUP-ID-WHEN-CONSP))
 (912 48 (:REWRITE AIGNET::BOUND-WHEN-AIGNET-IDP))
 (672 48 (:REWRITE AIGNET::LOOKUP-ID-IMPLIES-AIGNET-IDP))
 (608 40 (:LINEAR AIGNET::FANIN-COUNT-OF-CDR-LOOKUP-BOUND-BY-ID))
 (568 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-CDR))
 (528 48 (:LINEAR AIGNET::FANIN-ID-LTE-FANIN-COUNT-STRONG))
 (528 40 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-INVERSE))
 (400 80 (:REWRITE NFIX-WHEN-NATP))
 (392 8 (:REWRITE SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES))
 (304 80 (:REWRITE NFIX-WHEN-NOT-NATP))
 (276 276 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (276 276 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (276 276 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (276 276 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 (192 192 (:TYPE-PRESCRIPTION NATP))
 (192 96 (:REWRITE NATP-WHEN-GTE-0))
 (184 184 (:TYPE-PRESCRIPTION AIGNET-EXTENSION-P))
 (160 32 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (144 96 (:REWRITE DEFAULT-<-2))
 (144 96 (:REWRITE DEFAULT-<-1))
 (135 12 (:REWRITE DEFAULT-CAR))
 (132 132 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (132 132 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (96 96 (:TYPE-PRESCRIPTION AIGNET::AIGNET-IDP))
 (96 96 (:REWRITE NATP-WHEN-INTEGERP))
 (80 80 (:REWRITE AIGNET::AIGNET-EXTENSION-P-TRANSITIVE-RW))
 (72 72 (:LINEAR AIGNET::AIGNET-EXTENSION-IMPLIES-FANIN-COUNT-GTE))
 (67 12 (:REWRITE AIGNET::STYPE-BY-CTYPE))
 (64 64 (:REWRITE AIGNET::LOOKUP-ID-AIGNET-EXTENSION-P))
 (56 56 (:LINEAR AIGNET::FANIN-COUNT-WHEN-AIGNET-EXTENSION))
 (48 48 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (48 48 (:REWRITE AIGNET::AIGNET-IDP-IN-EXTENSION))
 (48 48 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-AIGNET-IDP))
 (48 48 (:LINEAR LISTPOS-COMPLETE))
 (40 40 (:REWRITE AIGNET::AIGNET-EXTENSION-P-SELF))
 (40 40 (:LINEAR AIGNET::FANIN-COUNT-CDR-WHEN-AIGNET-EXTENSION-STRONG))
 (12 12 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (12 12 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (12 12 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (8 8 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-NEGATED-HYP))
 (8 8 (:REWRITE SATLINK::EQUAL-OF-LIT->VAR-EQUAL-HYP))
 (4 1 (:REWRITE AIGNET::NODE-LIST-FIX-WHEN-NODE-LISTP))
 (1 1 (:REWRITE AIGNET::NODE-LISTP-WHEN-NOT-CONSP))
 )
(AIGNET::ID-IS-XOR-NODE-LIST-EQUIV-CONGRUENCE-ON-AIGNET)
(AIGNET::LIT-IS-XOR)
(AIGNET::LITP-OF-LIT-IS-XOR.CHILD1
 (2 2 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (2 2 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 )
(AIGNET::LITP-OF-LIT-IS-XOR.CHILD2
 (2 2 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (2 2 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 )
(AIGNET::AIGNET-LITP-OF-LIT-IS-XOR
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (4 4 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 )
(AIGNET::LIT-EVAL-WHEN-LIT-IS-XOR
 (127 12 (:REWRITE BFIX-WHEN-NOT-1))
 (32 12 (:REWRITE BFIX-WHEN-NOT-BITP))
 (24 24 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (24 12 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (24 12 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (15 3 (:LINEAR SATLINK::LIT->NEG-BOUND))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (7 7 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (7 7 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (5 5 (:REWRITE AIGNET::LIT-EVAL-PRESERVED-BY-EXTENSION-INVERSE))
 (5 5 (:REWRITE AIGNET::LIT-EVAL-PRESERVED-BY-EXTENSION))
 )
(AIGNET::LIT-IS-XOR-NOT-XOR-IMPLIES-AND
 (40 4 (:REWRITE DEFAULT-CAR))
 (27 9 (:TYPE-PRESCRIPTION AIGNET::TRUE-LISTP-LOOKUP-ID-OF-NODE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION SATLINK::VARP-OF-LIT->VAR))
 (9 9 (:TYPE-PRESCRIPTION AIGNET::NODE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION AIGNET::LOOKUP-ID))
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (4 4 (:REWRITE AIGNET::LOOKUP-ID-OF-FANIN-COUNT-BIND))
 (4 4 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION-INVERSE))
 (4 4 (:REWRITE AIGNET::LOOKUP-ID-IN-EXTENSION))
 (4 4 (:REWRITE AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-ID))
 )
(AIGNET::LIT-ID-BOUND-OF-LIT-IS-XOR-CHILD1
 (6 6 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (2 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(AIGNET::LIT-ID-BOUND-OF-LIT-IS-XOR-CHILD2
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (2 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(AIGNET::LIT-IS-XOR-OF-LIT-FIX-LIT
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES))
 (5 5 (:REWRITE SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES))
 (3 1 (:REWRITE SATLINK::LIT-FIX-OF-LIT))
 (2 2 (:TYPE-PRESCRIPTION SATLINK::LITP))
 )
(AIGNET::LIT-IS-XOR-LIT-EQUIV-CONGRUENCE-ON-LIT)
(AIGNET::LIT-IS-XOR-OF-NODE-LIST-FIX-AIGNET)
(AIGNET::LIT-IS-XOR-NODE-LIST-EQUIV-CONGRUENCE-ON-AIGNET)
