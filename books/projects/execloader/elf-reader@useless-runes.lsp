(EXLD::ELF-READ-MEM-NULL-TERM
 (250 16 (:DEFINITION LEN))
 (134 32 (:REWRITE LEN-WHEN-ATOM))
 (132 2 (:DEFINITION NTH))
 (100 4 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (44 4 (:REWRITE NTH-WHEN-ZP))
 (43 35 (:REWRITE DEFAULT-<-2))
 (42 26 (:REWRITE DEFAULT-+-2))
 (41 41 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (41 41 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (41 41 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (41 41 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (41 41 (:REWRITE CONSP-BY-LEN))
 (36 35 (:REWRITE DEFAULT-<-1))
 (32 6 (:REWRITE ZP-WHEN-INTEGERP))
 (26 26 (:REWRITE DEFAULT-+-1))
 (26 4 (:REWRITE NTH-WHEN-ATOM))
 (25 7 (:REWRITE NFIX-WHEN-NOT-NATP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (18 6 (:REWRITE ZP-WHEN-GT-0))
 (16 16 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (12 12 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (12 4 (:REWRITE NATP-WHEN-INTEGERP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 2 (:REWRITE NTH-WHEN-PREFIXP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 )
(EXLD::BYTE-LISTP-OF-ELF-READ-MEM-NULL-TERM
 (479 34 (:DEFINITION LEN))
 (450 18 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (234 68 (:REWRITE LEN-WHEN-ATOM))
 (194 18 (:REWRITE NTH-WHEN-ZP))
 (176 24 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (158 158 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (158 158 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (158 158 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (158 158 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (158 158 (:REWRITE CONSP-BY-LEN))
 (145 124 (:REWRITE DEFAULT-<-2))
 (144 21 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (133 21 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (124 124 (:REWRITE DEFAULT-<-1))
 (117 18 (:REWRITE NTH-WHEN-ATOM))
 (91 33 (:REWRITE ZP-WHEN-GT-0))
 (83 49 (:REWRITE DEFAULT-+-2))
 (70 2 (:DEFINITION NTHCDR))
 (64 2 (:REWRITE SUBSETP-OF-CONS))
 (56 46 (:REWRITE DEFAULT-CDR))
 (49 49 (:REWRITE DEFAULT-+-1))
 (44 4 (:REWRITE NTHCDR-WHEN-ZP))
 (40 40 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (40 40 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (40 40 (:LINEAR LEN-WHEN-PREFIXP))
 (36 36 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (26 26 (:REWRITE SUBSETP-TRANS2))
 (26 26 (:REWRITE SUBSETP-TRANS))
 (26 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (22 22 (:TYPE-PRESCRIPTION ZP))
 (22 1 (:REWRITE MEMBER-OF-NTH))
 (20 20 (:REWRITE NFIX-WHEN-NOT-NATP))
 (20 20 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (16 16 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (15 1 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE NTH-WHEN-PREFIXP))
 (7 7 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
 )
(EXLD::ELF-READ-STRING-NULL-TERM)
(EXLD::STRINGP-OF-ELF-READ-STRING-NULL-TERM)
(EXLD::READ-SEGMENT-HEADERS-64
 (200 2 (:DEFINITION MEMBER-EQUAL))
 (140 2 (:REWRITE EXLD::EQUAL-OF-ELF64-SEGMENT-HEADER))
 (113 4 (:REWRITE EXLD::ELF64-SEGMENT-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF64-SEGMENT-HEADERS-P))
 (109 1 (:REWRITE SUBSETP-OF-CONS))
 (32 16 (:REWRITE NFIX-WHEN-NOT-NATP))
 (32 16 (:REWRITE NFIX-WHEN-NATP))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 2 (:REWRITE EXLD::ELF64-SEGMENT-HEADERS-P-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->VADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->TYPE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->PADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->OFFSET$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->MEMSZ$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->FLAGS$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->FILESZ$INLINE))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 3 (:REWRITE ZP-WHEN-GT-0))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->ALIGN$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EXLD::ELF64-SEGMENT-HEADERS-P-OF-READ-SEGMENT-HEADERS-64
 (200 2 (:DEFINITION MEMBER-EQUAL))
 (140 2 (:REWRITE EXLD::EQUAL-OF-ELF64-SEGMENT-HEADER))
 (130 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (124 17 (:REWRITE EXLD::ELF64-SEGMENT-HEADERS-P-WHEN-NOT-CONSP))
 (122 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (113 4 (:REWRITE EXLD::ELF64-SEGMENT-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF64-SEGMENT-HEADERS-P))
 (109 1 (:REWRITE SUBSETP-OF-CONS))
 (78 78 (:TYPE-PRESCRIPTION EXLD::NATP-OF-MERGE-FIRST-SPLIT-BYTES.MERGED-NUM))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (53 53 (:REWRITE CONSP-BY-LEN))
 (32 16 (:REWRITE NFIX-WHEN-NOT-NATP))
 (32 16 (:REWRITE NFIX-WHEN-NATP))
 (25 25 (:REWRITE SUBSETP-TRANS2))
 (25 25 (:REWRITE SUBSETP-TRANS))
 (21 7 (:REWRITE ZP-WHEN-GT-0))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (7 7 (:REWRITE ZP-WHEN-INTEGERP))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->VADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->TYPE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->PADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->OFFSET$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->MEMSZ$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->FLAGS$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->FILESZ$INLINE))
 (6 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (6 1 (:REWRITE CONSP-OF-REV))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF64-SEGMENT-HEADER->ALIGN$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EXLD::READ-SEGMENT-HEADERS-32
 (200 2 (:DEFINITION MEMBER-EQUAL))
 (140 2 (:REWRITE EXLD::EQUAL-OF-ELF32-SEGMENT-HEADER))
 (113 4 (:REWRITE EXLD::ELF32-SEGMENT-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF32-SEGMENT-HEADERS-P))
 (109 1 (:REWRITE SUBSETP-OF-CONS))
 (32 16 (:REWRITE NFIX-WHEN-NOT-NATP))
 (32 16 (:REWRITE NFIX-WHEN-NATP))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 2 (:REWRITE EXLD::ELF32-SEGMENT-HEADERS-P-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->VADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->TYPE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->PADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->OFFSET$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->MEMSZ$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->FLAGS$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->FILESZ$INLINE))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 3 (:REWRITE ZP-WHEN-GT-0))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->ALIGN$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EXLD::ELF32-SEGMENT-HEADERS-P-OF-READ-SEGMENT-HEADERS-32
 (200 2 (:DEFINITION MEMBER-EQUAL))
 (140 2 (:REWRITE EXLD::EQUAL-OF-ELF32-SEGMENT-HEADER))
 (130 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (124 17 (:REWRITE EXLD::ELF32-SEGMENT-HEADERS-P-WHEN-NOT-CONSP))
 (122 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (113 4 (:REWRITE EXLD::ELF32-SEGMENT-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF32-SEGMENT-HEADERS-P))
 (109 1 (:REWRITE SUBSETP-OF-CONS))
 (78 78 (:TYPE-PRESCRIPTION EXLD::NATP-OF-MERGE-FIRST-SPLIT-BYTES.MERGED-NUM))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (53 53 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (53 53 (:REWRITE CONSP-BY-LEN))
 (32 16 (:REWRITE NFIX-WHEN-NOT-NATP))
 (32 16 (:REWRITE NFIX-WHEN-NATP))
 (25 25 (:REWRITE SUBSETP-TRANS2))
 (25 25 (:REWRITE SUBSETP-TRANS))
 (21 7 (:REWRITE ZP-WHEN-GT-0))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (7 7 (:REWRITE ZP-WHEN-INTEGERP))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->VADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->TYPE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->PADDR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->OFFSET$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->MEMSZ$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->FLAGS$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->FILESZ$INLINE))
 (6 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (6 1 (:REWRITE CONSP-OF-REV))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF32-SEGMENT-HEADER->ALIGN$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EXLD::READ-SECTION-HEADERS
 (246 2 (:DEFINITION MEMBER-EQUAL))
 (176 2 (:REWRITE EXLD::EQUAL-OF-ELF-SECTION-HEADER))
 (136 4 (:REWRITE EXLD::ELF-SECTION-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF-SECTION-HEADERS-P))
 (132 1 (:REWRITE SUBSETP-OF-CONS))
 (40 20 (:REWRITE NFIX-WHEN-NOT-NATP))
 (40 20 (:REWRITE NFIX-WHEN-NATP))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (7 2 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->TYPE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->SIZE$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->OFFSET$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME-STR$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->LINK$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->INFO$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->FLAGS$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDRALIGN$INLINE))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDR$INLINE))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 4 (:REWRITE ZP-WHEN-GT-0))
 (6 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ENTSIZE$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EXLD::ELF-SECTION-HEADERS-P-OF-READ-SECTION-HEADERS
 (492 4 (:DEFINITION MEMBER-EQUAL))
 (352 4 (:REWRITE EXLD::EQUAL-OF-ELF-SECTION-HEADER))
 (319 45 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (311 42 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (302 45 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (272 8 (:REWRITE EXLD::ELF-SECTION-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF-SECTION-HEADERS-P))
 (264 2 (:REWRITE SUBSETP-OF-CONS))
 (196 196 (:TYPE-PRESCRIPTION EXLD::NATP-OF-MERGE-FIRST-SPLIT-BYTES.MERGED-NUM))
 (130 130 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (130 130 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (130 130 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (130 130 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (130 130 (:REWRITE CONSP-BY-LEN))
 (80 40 (:REWRITE NFIX-WHEN-NOT-NATP))
 (80 40 (:REWRITE NFIX-WHEN-NATP))
 (59 59 (:REWRITE SUBSETP-TRANS2))
 (59 59 (:REWRITE SUBSETP-TRANS))
 (48 16 (:REWRITE ZP-WHEN-GT-0))
 (26 26 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (20 4 (:REWRITE SUBSETP-CAR-MEMBER))
 (16 16 (:REWRITE ZP-WHEN-INTEGERP))
 (16 16 (:REWRITE ZP-OPEN))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->TYPE$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->SIZE$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->OFFSET$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME-STR$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->LINK$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->INFO$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->FLAGS$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDRALIGN$INLINE))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDR$INLINE))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 2 (:REWRITE REV-WHEN-NOT-CONSP))
 (12 2 (:REWRITE CONSP-OF-REV))
 (8 8 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ENTSIZE$INLINE))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(EXLD::READ-ELF-HEADER)
(EXLD::ELF-HEADER-P-OF-READ-ELF-HEADER)
(EXLD::READ-SECTION-NAMES
 (414 4 (:DEFINITION MEMBER-EQUAL))
 (320 4 (:REWRITE EXLD::EQUAL-OF-ELF-SECTION-HEADER))
 (231 2 (:REWRITE SUBSETP-OF-CONS))
 (80 40 (:REWRITE NFIX-WHEN-NOT-NATP))
 (80 40 (:REWRITE NFIX-WHEN-NATP))
 (68 4 (:DEFINITION LEN))
 (37 8 (:REWRITE LEN-WHEN-ATOM))
 (21 21 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (21 21 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (21 21 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (21 21 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (21 21 (:REWRITE CONSP-BY-LEN))
 (21 6 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (16 6 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (14 14 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME-STR$INLINE))
 (13 3 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 4 (:REWRITE STR-FIX-WHEN-STRINGP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(EXLD::ELF-SECTION-HEADERS-P-OF-READ-SECTION-NAMES
 (256 2 (:DEFINITION MEMBER-EQUAL))
 (184 2 (:REWRITE EXLD::EQUAL-OF-ELF-SECTION-HEADER))
 (170 10 (:DEFINITION LEN))
 (149 25 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (141 4 (:REWRITE EXLD::ELF-SECTION-HEADER-P-WHEN-MEMBER-EQUAL-OF-ELF-SECTION-HEADERS-P))
 (137 1 (:REWRITE SUBSETP-OF-CONS))
 (130 20 (:REWRITE LEN-WHEN-ATOM))
 (117 23 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (93 23 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (89 89 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (89 89 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (89 89 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (89 89 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (89 89 (:REWRITE CONSP-BY-LEN))
 (40 20 (:REWRITE NFIX-WHEN-NOT-NATP))
 (40 20 (:REWRITE NFIX-WHEN-NATP))
 (38 38 (:REWRITE DEFAULT-CAR))
 (31 31 (:REWRITE SUBSETP-TRANS2))
 (31 31 (:REWRITE SUBSETP-TRANS))
 (20 10 (:REWRITE DEFAULT-<-1))
 (20 10 (:REWRITE DEFAULT-+-2))
 (19 10 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->TYPE$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->SIZE$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->OFFSET$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->LINK$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->INFO$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->FLAGS$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDRALIGN$INLINE))
 (16 16 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ADDR$INLINE))
 (16 16 (:REWRITE DEFAULT-CDR))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->ENTSIZE$INLINE))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (10 10 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (10 10 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (10 10 (:LINEAR LEN-WHEN-PREFIXP))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (8 8 (:TYPE-PRESCRIPTION EXLD::STRINGP-OF-ELF-READ-STRING-NULL-TERM))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF-SECTION-HEADER->NAME-STR$INLINE))
 (5 5 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(EXLD::BYTE-LISTP-OF-MAKE-LIST-AC-0
 (11 1 (:REWRITE REPEAT-WHEN-ZP))
 (6 1 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE ZP-WHEN-GT-0))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(EXLD::GET-STRING-SECTION-DATA
 (108 7 (:DEFINITION LEN))
 (79 2 (:DEFINITION NTHCDR))
 (66 1 (:DEFINITION NTH))
 (61 9 (:REWRITE ZP-WHEN-INTEGERP))
 (61 4 (:REWRITE NTHCDR-WHEN-ZP))
 (59 14 (:REWRITE LEN-WHEN-ATOM))
 (57 2 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (44 35 (:REWRITE DEFAULT-<-2))
 (37 35 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (29 29 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (29 29 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (29 29 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (29 29 (:REWRITE CONSP-BY-LEN))
 (29 9 (:REWRITE ZP-WHEN-GT-0))
 (26 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (22 2 (:REWRITE NTH-WHEN-ZP))
 (20 10 (:REWRITE DEFAULT-CDR))
 (19 12 (:REWRITE DEFAULT-+-2))
 (13 2 (:REWRITE NTH-WHEN-ATOM))
 (12 12 (:REWRITE DEFAULT-+-1))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (7 7 (:REWRITE NFIX-WHEN-NOT-NATP))
 (6 6 (:TYPE-PRESCRIPTION ZP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 1 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (4 4 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
 (2 2 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (2 2 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE NTH-WHEN-PREFIXP))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(EXLD::BYTE-LISTP-OF-GET-STRING-SECTION-DATA
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(EXLD::GET-NAMED-SECTION-HEADERS
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(EXLD::ELF-SECTION-HEADERS-P-OF-GET-NAMED-SECTION-HEADERS
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 )
(EXLD::IS-ELF-CONTENT-P
 (123 7 (:DEFINITION LEN))
 (103 1 (:DEFINITION TAKE))
 (77 2 (:REWRITE TAKE-OF-TOO-MANY))
 (75 2 (:REWRITE TAKE-OF-LEN-FREE))
 (74 14 (:REWRITE LEN-WHEN-ATOM))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (22 22 (:REWRITE CONSP-BY-LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 8 (:REWRITE DEFAULT-CDR))
 (13 2 (:REWRITE TAKE-WHEN-ATOM))
 (12 12 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (12 12 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (11 11 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (6 1 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (5 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION NFIX))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 )
(EXLD::BOOLEANP-OF-IS-ELF-CONTENT-P.IS-ELF-FILE
 (103 1 (:DEFINITION TAKE))
 (89 5 (:DEFINITION LEN))
 (77 2 (:REWRITE TAKE-OF-TOO-MANY))
 (75 2 (:REWRITE TAKE-OF-LEN-FREE))
 (58 10 (:REWRITE LEN-WHEN-ATOM))
 (55 55 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (55 55 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (17 17 (:REWRITE CONSP-BY-LEN))
 (13 2 (:REWRITE TAKE-WHEN-ATOM))
 (12 12 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (12 12 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (11 6 (:REWRITE DEFAULT-CDR))
 (10 5 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT BYTE-LIST-FIX-UNDER-BYTE-LIST-EQUIV))
 (6 6 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (6 1 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-<-2))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE SUBSETP-MEMBER . 4))
 (3 3 (:REWRITE SUBSETP-MEMBER . 3))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:TYPE-PRESCRIPTION NFIX))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
(EXLD::ELF-HEADER-P-OF-IS-ELF-CONTENT-P.HEADER
 (103 1 (:DEFINITION TAKE))
 (89 5 (:DEFINITION LEN))
 (77 2 (:REWRITE TAKE-OF-TOO-MANY))
 (75 2 (:REWRITE TAKE-OF-LEN-FREE))
 (58 10 (:REWRITE LEN-WHEN-ATOM))
 (55 55 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (55 55 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (17 17 (:REWRITE CONSP-BY-LEN))
 (13 2 (:REWRITE TAKE-WHEN-ATOM))
 (12 12 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (12 12 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (11 6 (:REWRITE DEFAULT-CDR))
 (10 5 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT BYTE-LIST-FIX-UNDER-BYTE-LIST-EQUIV))
 (6 6 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (6 1 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-<-2))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE SUBSETP-MEMBER . 4))
 (3 3 (:REWRITE SUBSETP-MEMBER . 3))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:TYPE-PRESCRIPTION NFIX))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
(EXLD::SET-ELF-STOBJ-FIELDS
 (245 1 (:DEFINITION TAKE))
 (220 2 (:REWRITE TAKE-OF-TOO-MANY))
 (193 11 (:DEFINITION LEN))
 (185 5 (:DEFINITION NTHCDR))
 (152 27 (:REWRITE LEN-WHEN-ATOM))
 (130 3 (:REWRITE CONSP-OF-NTHCDR))
 (113 2 (:REWRITE TAKE-OF-LEN-FREE))
 (96 18 (:REWRITE DEFAULT-CDR))
 (69 14 (:REWRITE ZP-WHEN-INTEGERP))
 (69 10 (:REWRITE NTHCDR-WHEN-ZP))
 (64 64 (:TYPE-PRESCRIPTION LEN))
 (64 1 (:REWRITE CAR-OF-NTHCDR))
 (63 2 (:REWRITE TAKE-WHEN-ATOM))
 (62 19 (:REWRITE NFIX-WHEN-NOT-NATP))
 (57 36 (:REWRITE DEFAULT-<-2))
 (52 36 (:REWRITE DEFAULT-<-1))
 (50 14 (:REWRITE ZP-WHEN-GT-0))
 (45 10 (:REWRITE NTHCDR-WHEN-ATOM))
 (44 44 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (44 44 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (44 44 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (44 44 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (44 44 (:REWRITE CONSP-BY-LEN))
 (43 27 (:REWRITE DEFAULT-+-2))
 (36 1 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (32 27 (:REWRITE DEFAULT-+-1))
 (32 2 (:REWRITE NATP-WHEN-INTEGERP))
 (20 1 (:REWRITE NTH-WHEN-ZP))
 (20 1 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (19 19 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (16 16 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (16 16 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (16 16 (:LINEAR LEN-WHEN-PREFIXP))
 (15 5 (:REWRITE COMMUTATIVITY-OF-+))
 (15 2 (:REWRITE NATP-WHEN-GTE-0))
 (10 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:TYPE-PRESCRIPTION ZP))
 (8 8 (:REWRITE SUBSETP-TRANS2))
 (8 8 (:REWRITE SUBSETP-TRANS))
 (8 8 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 1 (:REWRITE NTH-WHEN-ATOM))
 (6 1 (:REWRITE EXLD::ELF-SECTION-HEADERS-P-WHEN-NOT-CONSP))
 (6 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE OPEN-SMALL-NTHCDR))
 (4 4 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (3 3 (:LINEAR LISTPOS-COMPLETE))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE EXLD::SECTION-INFO-P-WHEN-MEMBER-EQUAL-OF-SECTION-INFO-LIST-P))
 (2 2 (:REWRITE EXLD::SECTION-INFO-LIST-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:REWRITE EXLD::SECTION-INFO-LIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE NTH-WHEN-PREFIXP))
 (1 1 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 )
(EXLD::GOOD-ELF-P-OF-SET-ELF-STOBJ-FIELDS)
(EXLD::POPULATE-ELF-CONTENTS
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(EXLD::GOOD-ELF-P-OF-POPULATE-ELF-CONTENTS.NEW-ELF)
(EXLD::POPULATE-ELF)
(EXLD::GOOD-ELF-P-OF-POPULATE-ELF.NEW-ELF)
(EXLD::PARSE-SYMTAB-ENTRIES
 (175 14 (:REWRITE EXLD::ELF64_SYM-P-WHEN-UNSIGNED-BYTE-P))
 (175 14 (:REWRITE EXLD::ELF32_SYM-P-WHEN-UNSIGNED-BYTE-P))
 (159 3 (:DEFINITION NTHCDR))
 (154 14 (:DEFINITION UNSIGNED-BYTE-P))
 (140 14 (:DEFINITION INTEGER-RANGE-P))
 (129 11 (:REWRITE NFIX-WHEN-NOT-NATP))
 (113 9 (:DEFINITION LEN))
 (104 64 (:REWRITE DEFAULT-<-1))
 (88 6 (:REWRITE NTHCDR-WHEN-ZP))
 (82 7 (:REWRITE ZP-WHEN-INTEGERP))
 (80 64 (:REWRITE DEFAULT-<-2))
 (77 18 (:REWRITE LEN-WHEN-ATOM))
 (56 7 (:REWRITE EXLD::UNSIGNED-BYTE-P-WHEN-ELF64_SYM-P))
 (56 7 (:REWRITE EXLD::UNSIGNED-BYTE-P-WHEN-ELF32_SYM-P))
 (42 14 (:REWRITE EXLD::WIDTH-OF-MV-NTH-0-MERGE-FIRST-SPLIT-BYTES))
 (34 21 (:REWRITE DEFAULT-+-2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (33 33 (:REWRITE CONSP-BY-LEN))
 (32 32 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (31 7 (:REWRITE ZP-WHEN-GT-0))
 (29 6 (:REWRITE NTHCDR-WHEN-ATOM))
 (28 28 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (28 28 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (28 28 (:LINEAR LEN-WHEN-PREFIXP))
 (27 12 (:REWRITE DEFAULT-CDR))
 (25 5 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (23 21 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (14 14 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (14 14 (:REWRITE DEFAULT-*-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (14 14 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (12 12 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (12 2 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (9 9 (:REWRITE SUBSETP-TRANS2))
 (9 9 (:REWRITE SUBSETP-TRANS))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
 (3 3 (:LINEAR LISTPOS-COMPLETE))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE EXLD::ELF64_SYM->NAME-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE EXLD::ELF32_SYM->NAME-OF-WRITE-WITH-MASK))
 )
(EXLD::ELF64_SYM-INFO-LIST-P-OF-PARSE-SYMTAB-ENTRIES
 (132 3 (:DEFINITION NTHCDR))
 (117 6 (:REWRITE NTHCDR-WHEN-ZP))
 (90 12 (:REWRITE ZP-WHEN-INTEGERP))
 (75 5 (:DEFINITION LEN))
 (72 72 (:TYPE-PRESCRIPTION EXLD::ELF64_SYM->NAME))
 (70 2 (:DEFINITION MEMBER-EQUAL))
 (51 39 (:REWRITE DEFAULT-<-2))
 (49 5 (:DEFINITION UNSIGNED-BYTE-P))
 (48 12 (:REWRITE ZP-WHEN-GT-0))
 (48 4 (:REWRITE EXLD::ELF64_SYM-INFO-P-WHEN-MEMBER-EQUAL-OF-ELF64_SYM-INFO-LIST-P))
 (44 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (44 5 (:DEFINITION INTEGER-RANGE-P))
 (44 1 (:REWRITE SUBSETP-OF-CONS))
 (43 39 (:REWRITE DEFAULT-<-1))
 (39 6 (:REWRITE NTHCDR-WHEN-ATOM))
 (32 2 (:REWRITE EXLD::EQUAL-OF-ELF64_SYM-INFO))
 (31 31 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (31 31 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (31 31 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (31 31 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (31 31 (:REWRITE CONSP-BY-LEN))
 (28 28 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (28 4 (:REWRITE EXLD::ELF64_SYM-INFO-LIST-P-WHEN-NOT-CONSP))
 (26 14 (:REWRITE NATP-WHEN-GTE-0))
 (25 10 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION NATP))
 (16 11 (:REWRITE DEFAULT-+-2))
 (15 5 (:REWRITE EXLD::WIDTH-OF-MV-NTH-0-MERGE-FIRST-SPLIT-BYTES))
 (14 14 (:REWRITE NATP-WHEN-INTEGERP))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (11 11 (:REWRITE DEFAULT-+-1))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (9 3 (:REWRITE COMMUTATIVITY-OF-+))
 (8 8 (:TYPE-PRESCRIPTION EXLD::BYTES->STRING))
 (8 8 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 6 (:TYPE-PRESCRIPTION ZP))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF64_SYM-INFO->NAME-STR$INLINE))
 (6 6 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF64_SYM-INFO->ENTRY$INLINE))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
 (3 3 (:REWRITE EXLD::ELF64_SYM->NAME-OF-WRITE-WITH-MASK))
 (2 2 (:REWRITE EXLD::ELF64_SYM-FIX-WHEN-ELF64_SYM-P))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:LINEAR LISTPOS-COMPLETE))
 )
(EXLD::ELF32_SYM-INFO-LIST-P-OF-PARSE-SYMTAB-ENTRIES
 (176 4 (:DEFINITION NTHCDR))
 (156 8 (:REWRITE NTHCDR-WHEN-ZP))
 (120 16 (:REWRITE ZP-WHEN-INTEGERP))
 (96 96 (:TYPE-PRESCRIPTION EXLD::ELF32_SYM->NAME))
 (92 6 (:DEFINITION LEN))
 (70 2 (:DEFINITION MEMBER-EQUAL))
 (65 49 (:REWRITE DEFAULT-<-2))
 (64 16 (:REWRITE ZP-WHEN-GT-0))
 (60 6 (:DEFINITION UNSIGNED-BYTE-P))
 (54 49 (:REWRITE DEFAULT-<-1))
 (54 6 (:DEFINITION INTEGER-RANGE-P))
 (52 8 (:REWRITE NTHCDR-WHEN-ATOM))
 (51 9 (:REWRITE NFIX-WHEN-NOT-NATP))
 (48 4 (:REWRITE EXLD::ELF32_SYM-INFO-P-WHEN-MEMBER-EQUAL-OF-ELF32_SYM-INFO-LIST-P))
 (44 1 (:REWRITE SUBSETP-OF-CONS))
 (39 39 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (39 39 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (39 39 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (39 39 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (39 39 (:REWRITE CONSP-BY-LEN))
 (38 5 (:REWRITE EXLD::ELF32_SYM-INFO-LIST-P-WHEN-NOT-CONSP))
 (32 32 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (32 12 (:REWRITE DEFAULT-CDR))
 (32 2 (:REWRITE EXLD::EQUAL-OF-ELF32_SYM-INFO))
 (30 16 (:REWRITE NATP-WHEN-GTE-0))
 (28 28 (:TYPE-PRESCRIPTION NATP))
 (20 14 (:REWRITE DEFAULT-+-2))
 (18 6 (:REWRITE EXLD::WIDTH-OF-MV-NTH-0-MERGE-FIRST-SPLIT-BYTES))
 (16 16 (:REWRITE NATP-WHEN-INTEGERP))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (8 8 (:TYPE-PRESCRIPTION ZP))
 (8 8 (:TYPE-PRESCRIPTION EXLD::BYTES->STRING))
 (7 7 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (6 6 (:TYPE-PRESCRIPTION EXLD::ELF32_SYM-INFO->NAME-STR$INLINE))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (4 4 (:TYPE-PRESCRIPTION EXLD::ELF32_SYM-INFO->ENTRY$INLINE))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
 (4 4 (:REWRITE EXLD::ELF32_SYM->NAME-OF-WRITE-WITH-MASK))
 (4 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 (2 2 (:REWRITE EXLD::ELF32_SYM-FIX-WHEN-ELF32_SYM-P))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:LINEAR LISTPOS-COMPLETE))
 )
(EXLD::GET-SYMTAB-ENTRIES)
(EXLD::ELF32_SYM-INFO-LIST-P-OF-GET-SYMTAB-ENTRIES)
(EXLD::ELF64_SYM-INFO-LIST-P-OF-GET-SYMTAB-ENTRIES)
(EXLD::FIND-LABEL-ADDRESS-FROM-ELF-SYMTAB-INFO
 (6 6 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (6 6 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (6 6 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (6 6 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (6 6 (:REWRITE CONSP-BY-LEN))
 (6 1 (:REWRITE EXLD::ELF64_SYM-INFO-LIST-P-WHEN-NOT-CONSP))
 (6 1 (:REWRITE EXLD::ELF32_SYM-INFO-LIST-P-WHEN-NOT-CONSP))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(EXLD::MAYBE-NATP-OF-FIND-LABEL-ADDRESS-FROM-ELF-SYMTAB-INFO)
(EXLD::GET-LABEL-ADDRESS)
(EXLD::MAYBE-NATP-OF-GET-LABEL-ADDRESS)
(EXLD::GET-LABEL-ADDRESSES
 (268 7 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (168 7 (:DEFINITION MEMBER-EQUAL))
 (91 14 (:REWRITE MEMBER-WHEN-ATOM))
 (35 35 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (22 22 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (22 22 (:REWRITE CONSP-BY-LEN))
 (16 16 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (14 14 (:REWRITE SUBSETP-MEMBER . 4))
 (14 14 (:REWRITE SUBSETP-MEMBER . 3))
 (14 14 (:REWRITE SUBSETP-MEMBER . 2))
 (14 14 (:REWRITE SUBSETP-MEMBER . 1))
 (14 14 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (14 14 (:REWRITE INTERSECTP-MEMBER . 3))
 (14 14 (:REWRITE INTERSECTP-MEMBER . 2))
 (12 12 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE VL::STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P))
 (8 8 (:REWRITE VL::STRINGP-OF-CAR-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P))
 (6 6 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 )
(EXLD::TRUE-LISTP-OF-GET-LABEL-ADDRESSES)