(SV::SVEX-ENV-REMOVE-XES
 (42 42 (:REWRITE DEFAULT-CAR))
 (40 10 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (10 10 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 )
(SV::SVEX-ENV-P-OF-SVEX-ENV-REMOVE-XES
 (146 50 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (113 9 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (101 11 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (61 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (61 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (61 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (45 44 (:REWRITE DEFAULT-CAR))
 (41 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (41 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (40 10 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (32 8 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (22 22 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (20 20 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (16 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::HONS-ASSOC-EQUAL-OF-SVEX-ENV-REMOVE-XES
 (8888 44 (:DEFINITION ALIST-KEYS))
 (8504 80 (:REWRITE SV::CONSP-CAR-OF-SVEX-ENV-FIX))
 (6111 2172 (:REWRITE DEFAULT-CAR))
 (4668 284 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (3353 408 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (3226 775 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (3066 247 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (2376 247 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (2376 247 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (2376 247 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (1653 1651 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (1624 246 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (1584 247 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (1584 247 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (1584 247 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (1400 280 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (894 149 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (894 149 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (894 149 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (840 840 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (792 792 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (792 792 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (792 792 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (596 149 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (596 149 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (572 572 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (560 560 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (560 560 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (560 280 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (494 494 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (396 396 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (396 396 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (396 396 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (396 396 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (396 396 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (257 92 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (247 247 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (240 34 (:REWRITE SV::4VEC-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVEX-ENV-P))
 (223 86 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (99 33 (:DEFINITION MEMBER-EQUAL))
 (86 86 (:REWRITE FN-CHECK-DEF-FORMALS))
 (44 44 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (28 28 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 )
(SV::SVEX-ENV-LOOKUP-OF-SVEX-ENV-REMOVE-XES
 (700 10 (:DEFINITION SV::SVEX-ENV-FIX$INLINE))
 (465 3 (:DEFINITION ALIST-KEYS))
 (441 6 (:REWRITE SV::CONSP-CAR-OF-SVEX-ENV-FIX))
 (308 110 (:REWRITE DEFAULT-CAR))
 (218 18 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (111 20 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (110 11 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (86 1 (:DEFINITION SV::SVEX-ENV-REMOVE-XES))
 (82 60 (:REWRITE DEFAULT-CDR))
 (80 16 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (66 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (66 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (66 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (52 52 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (48 48 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (48 12 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (44 11 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (44 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (44 11 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (40 10 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (39 3 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (34 34 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (32 32 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (32 32 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (32 16 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (28 8 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (22 22 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (22 22 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (22 22 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (22 22 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (21 21 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (16 1 (:DEFINITION SV::4VEC-EQUIV$INLINE))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (15 15 (:TYPE-PRESCRIPTION SV::SVEX-ENV-FIX$INLINE))
 (15 6 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (15 6 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (11 11 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (9 3 (:DEFINITION MEMBER-EQUAL))
 (8 2 (:REWRITE SV::4VEC-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVEX-ENV-P))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 3 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::SVEX-ENV-REMOVE-XES-UNDER-SVEX-ENVS-SIMILAR
 (13 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (5 2 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (4 1 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (4 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (3 3 (:TYPE-PRESCRIPTION SV::SVEX-ENV-FIX$INLINE))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION SV::SVEX-ENV-P))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 )
(SV::NO-DUPLICATE-KEYS-OF-SVEX-ENV-REMOVE-XES
 (1056 30 (:DEFINITION ALIST-KEYS))
 (774 30 (:REWRITE SV::CONSP-CAR-OF-SVEX-ENV-FIX))
 (703 343 (:REWRITE DEFAULT-CAR))
 (489 33 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (364 34 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (240 34 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (240 34 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (240 34 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (230 35 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (214 206 (:REWRITE DEFAULT-CDR))
 (183 75 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (166 40 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (160 34 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (160 34 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (160 34 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (160 32 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (154 60 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (138 137 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (136 28 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (105 105 (:TYPE-PRESCRIPTION SV::SVEX-ENV-FIX$INLINE))
 (96 96 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (80 80 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (80 80 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (80 80 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (78 26 (:DEFINITION MEMBER-EQUAL))
 (68 68 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (68 68 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (64 64 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (64 64 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (64 32 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (60 60 (:REWRITE FN-CHECK-DEF-FORMALS))
 (40 40 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (36 6 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (36 6 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (36 6 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (34 34 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (32 4 (:REWRITE SV::4VEC-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVEX-ENV-P))
 (30 30 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (24 6 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (24 6 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (5 5 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (5 5 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::NOT-SVEX-ENV-REMOVE-XES-WHEN-NOT-SVEX-ENV-FIX
 (196 14 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (160 16 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (96 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (96 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (96 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (82 82 (:REWRITE DEFAULT-CAR))
 (70 14 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (68 14 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (64 16 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (64 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (64 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (56 14 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (48 47 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (42 42 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (32 32 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (32 32 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (32 32 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (32 32 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (32 32 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (28 28 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (28 28 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (28 14 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (24 24 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (12 3 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::CAR-<<-OF-SVEX-ENV-REMOVE-XES
 (2714 265 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (2280 508 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (2006 132 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (1552 128 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (1168 128 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (1168 128 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (1168 128 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (999 997 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (886 831 (:REWRITE DEFAULT-CAR))
 (827 221 (:REWRITE <<-TRICHOTOMY))
 (784 128 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (784 128 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (784 128 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (776 122 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (721 132 (:REWRITE <<-ASYMMETRIC))
 (684 48 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (671 666 (:REWRITE DEFAULT-CDR))
 (610 122 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (400 64 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (400 64 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (400 64 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (384 384 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (384 384 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (384 384 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (366 366 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (300 48 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (272 64 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (272 64 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (256 256 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (256 256 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (244 244 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (244 244 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (244 122 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (240 48 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (192 192 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (192 192 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (192 192 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (192 192 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (192 192 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (192 192 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (156 96 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (144 48 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (128 128 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (96 96 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (96 96 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (96 48 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (96 48 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (48 48 (:REWRITE SET::IN-SET))
 (23 23 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (23 23 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::<<-TRANSITIVE-STRONG
 (52 23 (:REWRITE <<-TRICHOTOMY))
 (46 14 (:REWRITE <<-ASYMMETRIC))
 (31 20 (:REWRITE <<-TRANSITIVE))
 )
(SV::SETP-OF-SVEX-ENV-REMOVE-XES
 (994 114 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (820 58 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (815 53 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (780 185 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (661 151 (:REWRITE <<-TRICHOTOMY))
 (652 54 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (601 91 (:REWRITE <<-ASYMMETRIC))
 (492 54 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (492 54 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (492 54 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (399 397 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (375 375 (:REWRITE DEFAULT-CAR))
 (356 58 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (328 54 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (328 54 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (328 54 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (312 50 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (290 58 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (289 283 (:REWRITE DEFAULT-CDR))
 (250 50 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (232 232 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (182 116 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (174 58 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (168 28 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (168 28 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (168 28 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (164 164 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (164 164 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (164 164 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (151 151 (:REWRITE <<-TRANSITIVE))
 (150 150 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (116 116 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (116 116 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (116 58 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (116 58 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (112 28 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (112 28 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (108 108 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (108 108 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (100 100 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (100 100 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (100 50 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (82 82 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (82 82 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (82 82 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (82 82 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (82 82 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (58 58 (:REWRITE SET::IN-SET))
 (54 54 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (5 5 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (5 5 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::SVEX-ENV-REMOVE-XES-IDEMPOTENT
 (1974 126 (:REWRITE SV::NOT-SVEX-ENV-REMOVE-XES-WHEN-NOT-SVEX-ENV-FIX))
 (1760 78 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (315 75 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (240 23 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (206 199 (:REWRITE DEFAULT-CAR))
 (170 23 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (170 23 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (170 23 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (167 35 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (164 161 (:REWRITE DEFAULT-CDR))
 (150 32 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (142 141 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (112 21 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (70 70 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (66 66 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (66 33 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (56 56 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (56 56 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (56 56 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (55 1 (:REWRITE SV::SVEX-ENV-FIX-OF-ACONS))
 (46 46 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (42 42 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (42 7 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (42 7 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (42 7 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (37 37 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (28 28 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (28 28 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (28 28 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (28 28 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (28 7 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (28 7 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (27 27 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (27 27 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 (21 21 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 )
(SV::HONS-ASSOC-EQUAL-NON-X-OF-SVEX-ENV-REMOVE-XES
 (1079 28 (:REWRITE SV::HONS-ASSOC-EQUAL-OF-SVEX-ENV-REMOVE-XES))
 (768 74 (:REWRITE SV::NOT-SVEX-ENV-REMOVE-XES-WHEN-NOT-SVEX-ENV-FIX))
 (712 98 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (594 27 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (392 97 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (389 370 (:REWRITE DEFAULT-CAR))
 (290 264 (:REWRITE DEFAULT-CDR))
 (266 25 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (248 247 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (195 39 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (189 189 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (189 27 (:DEFINITION MEMBER-EQUAL))
 (188 39 (:REWRITE SV::4VEC-P-OF-CDAR-WHEN-SVEX-ENV-P))
 (174 25 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (174 25 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (174 25 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (135 135 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (135 54 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (116 25 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (116 25 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (116 25 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (108 27 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (78 78 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (78 78 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (78 39 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (58 58 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (58 58 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (58 58 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (54 54 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (54 54 (:REWRITE FN-CHECK-DEF-FORMALS))
 (50 50 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (29 29 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (29 29 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (29 29 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (29 29 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (29 29 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (27 27 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (25 25 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (24 4 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (24 4 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (24 4 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (18 18 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (18 18 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 (16 4 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (16 4 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 )
(SV::SVEX-ENV-REMOVE-XES-OF-SVEX-ENV-FIX-X
 (9753 487 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (8655 876 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (2564 182 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (2074 182 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (2034 182 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (2034 182 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (1806 1061 (:REWRITE DEFAULT-CAR))
 (1598 838 (:REWRITE DEFAULT-CDR))
 (1588 1575 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (1492 178 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (1484 189 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (1002 115 (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (986 115 (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (986 115 (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (772 115 (:REWRITE SV::SVARLIST-LIST-P-OF-CDR-WHEN-SVARLIST-LIST-P))
 (756 115 (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (602 122 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (586 586 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (586 586 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (586 586 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (364 364 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (356 356 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (300 300 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (293 293 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (293 293 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (293 293 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (293 293 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (244 244 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (240 240 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (240 120 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (178 178 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (100 2 (:REWRITE SV::SVEX-ENV-FIX-OF-ACONS))
 (15 15 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV))
 (15 15 (:REWRITE-QUOTED-CONSTANT SV::4VEC-FIX-UNDER-4VEC-EQUIV))
 )
(SV::SVEX-ENV-REMOVE-XES-SVEX-ENV-EQUIV-CONGRUENCE-ON-X)
(SV::SVEX-ENV-P-OF-ALIST-CANONICALIZE
 (46 9 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (32 5 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (30 3 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (25 22 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (19 19 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (18 3 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (18 3 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (18 3 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (16 4 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (13 13 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (12 3 (:REWRITE SV::SVEX-ENV-P-OF-CDR-WHEN-SVEX-ENV-P))
 (12 3 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (10 10 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (3 1 (:REWRITE ALIST-CANONICALIZE-WHEN-CANONICAL-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION CANONICAL-ALIST-P))
 )
(SV::ALISTP-WHEN-SVEX-ENV-P-RW)
(SV::SVEX-ENV-NORM)
(SV::SVEX-ENV-P-OF-SVEX-ENV-NORM)
(SV::SVEX-ENV-NORM-IDEMPOTENT
 (30 2 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (22 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (14 2 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (12 3 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (10 2 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (9 3 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (8 4 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (7 1 (:DEFINITION MEMBER-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (4 2 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (4 2 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (3 3 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (1 1 (:REWRITE SET::IN-SET))
 )
(SV::CANONICAL-ALIST-P-OF-SVEX-ENV-NORM
 (126 2 (:REWRITE ALIST-CANONICALIZE-WHEN-CANONICAL-ALIST-P))
 (45 3 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (44 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (21 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (16 4 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (14 5 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (14 2 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 2 (:REWRITE SV::ALISTP-WHEN-SVEX-ENV-P-RW))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (6 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (5 5 (:REWRITE FN-CHECK-DEF-FORMALS))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (2 2 (:REWRITE SET::IN-SET))
 )
(SV::SVEX-ENV-LOOKUP-OF-SVEX-ENV-NORM
 (25 3 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (20 11 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (10 2 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (9 3 (:REWRITE ALIST-CANONICALIZE-WHEN-CANONICAL-ALIST-P))
 (8 8 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (6 6 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (6 6 (:TYPE-PRESCRIPTION CANONICAL-ALIST-P))
 (6 6 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (5 5 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (4 4 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (4 2 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (4 1 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (4 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (4 1 (:REWRITE SV::4VEC-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVEX-ENV-P))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (3 3 (:REWRITE SV::LOOKUP-WHEN-SVEX-ENVS-AGREE))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 )
(SV::SVEX-ENV-NORM-UNDER-SVEX-ENVS-SIMILAR)
(SV::HONS-ASSOC-EQUAL-NON-X-OF-SVEX-ENV-NORM
 (8 8 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (3 1 (:REWRITE ALIST-CANONICALIZE-WHEN-CANONICAL-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION CANONICAL-ALIST-P))
 (1 1 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 )
(SV::SVEX-ENV-NORM-OF-SVEX-ENV-FIX-X)
(SV::SVEX-ENV-NORM-SVEX-ENV-EQUIV-CONGRUENCE-ON-X)
(SV::SVEX-ENV-NORMEDP)
(SV::SVEX-ENV-NORMEDP-OF-SVEX-ENV-NORM)
(SV::SVEX-ENV-NORM-WHEN-SVEX-ENV-NORMEDP)
(SV::CANONICAL-ALIST-P-WHEN-SVEX-ENV-NORMEDP
 (27 6 (:REWRITE SV::SVEX-ENV-NORM-WHEN-SVEX-ENV-NORMEDP))
 (3 3 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 )
(SV::HONS-ASSOC-EQUAL-NON-X-WHEN-SVEX-ENV-NORMED
 (16 2 (:DEFINITION HONS-ASSOC-EQUAL))
 (8 8 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 2 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (4 4 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (2 2 (:DEFINITION HONS-EQUAL))
 (1 1 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 )
(SV::SVEX-ENV-NORMEDP-OF-SVEX-ENV-FIX-X)
(SV::SVEX-ENV-NORMEDP-SVEX-ENV-EQUIV-CONGRUENCE-ON-X)
(SV::SVEX-ENV-NORMEDP-KEY-DIFF
 (4 4 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 )
(SV::LOOKUP-OF-SVEX-ENV-NORMEDP-KEY-DIFF
 (102 36 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (99 8 (:REWRITE SV::4VEC-FIX-OF-4VEC))
 (48 48 (:REWRITE DEFAULT-CAR))
 (35 7 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (32 32 (:REWRITE DEFAULT-CDR))
 (29 29 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (28 7 (:REWRITE SV::4VEC-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVEX-ENV-P))
 (21 21 (:TYPE-PRESCRIPTION SV::4VEC-P))
 (14 14 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (14 14 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (14 7 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (6 6 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 )
(SV::SVEX-ENV-NORMEDP-KEY-DIFF-OF-SVEX-ENV-FIX-X)
(SV::SVEX-ENV-NORMEDP-KEY-DIFF-SVEX-ENV-EQUIV-CONGRUENCE-ON-X)
(SV::SVEX-ENV-NORMEDP-KEY-DIFF-OF-SVEX-ENV-FIX-Y)
(SV::SVEX-ENV-NORMEDP-KEY-DIFF-SVEX-ENV-EQUIV-CONGRUENCE-ON-Y)
