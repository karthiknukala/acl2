(JAVA::UNICODE-STRINGLIT-CHAR-P)
(JAVA::BOOLEANP-OF-UNICODE-STRINGLIT-CHAR-P)
(JAVA::UNICODE-STRINGLIT-CHAR-FIX
     (1 1
        (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(JAVA::UNICODE-STRINGLIT-CHAR-P-OF-UNICODE-STRINGLIT-CHAR-FIX
     (3 3
        (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P
     (19 19
         (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (33 33
         (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(JAVA::UNICODE-STRINGLIT-CHAR-EQUIV$INLINE
     (4 4
        (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(JAVA::UNICODE-STRINGLIT-CHAR-EQUIV-IS-AN-EQUIVALENCE)
(JAVA::UNICODE-STRINGLIT-CHAR-EQUIV-IMPLIES-EQUAL-UNICODE-STRINGLIT-CHAR-FIX-1)
(JAVA::UNICODE-STRINGLIT-CHAR-FIX-UNDER-UNICODE-STRINGLIT-CHAR-EQUIV)
(JAVA::EQUAL-OF-UNICODE-STRINGLIT-CHAR-FIX-1-FORWARD-TO-UNICODE-STRINGLIT-CHAR-EQUIV)
(JAVA::EQUAL-OF-UNICODE-STRINGLIT-CHAR-FIX-2-FORWARD-TO-UNICODE-STRINGLIT-CHAR-EQUIV)
(JAVA::UNICODE-STRINGLIT-CHAR-EQUIV-OF-UNICODE-STRINGLIT-CHAR-FIX-1-FORWARD)
(JAVA::UNICODE-STRINGLIT-CHAR-EQUIV-OF-UNICODE-STRINGLIT-CHAR-FIX-2-FORWARD)
(JAVA::STRING-LITERAL-CHAR-P)
(JAVA::CONSP-WHEN-STRING-LITERAL-CHAR-P)
(JAVA::STRING-LITERAL-CHAR-KIND$INLINE)
(JAVA::STRING-LITERAL-CHAR-KIND-POSSIBILITIES)
(JAVA::STRING-LITERAL-CHAR-FIX$INLINE
     (6 6
        (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(JAVA::STRING-LITERAL-CHAR-P-OF-STRING-LITERAL-CHAR-FIX
 (12
   4
   (:REWRITE JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P))
 (12 4
     (:REWRITE JAVA::ESCAPE-SEQUENCE-FIX-WHEN-ESCAPE-SEQUENCE-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::ESCAPE-SEQUENCE-P)))
(JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P)
(JAVA::STRING-LITERAL-CHAR-FIX$INLINE
     (6 6
        (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(JAVA::STRING-LITERAL-CHAR-EQUIV$INLINE)
(JAVA::STRING-LITERAL-CHAR-EQUIV-IS-AN-EQUIVALENCE)
(JAVA::STRING-LITERAL-CHAR-EQUIV-IMPLIES-EQUAL-STRING-LITERAL-CHAR-FIX-1)
(JAVA::STRING-LITERAL-CHAR-FIX-UNDER-STRING-LITERAL-CHAR-EQUIV)
(JAVA::EQUAL-OF-STRING-LITERAL-CHAR-FIX-1-FORWARD-TO-STRING-LITERAL-CHAR-EQUIV)
(JAVA::EQUAL-OF-STRING-LITERAL-CHAR-FIX-2-FORWARD-TO-STRING-LITERAL-CHAR-EQUIV)
(JAVA::STRING-LITERAL-CHAR-EQUIV-OF-STRING-LITERAL-CHAR-FIX-1-FORWARD)
(JAVA::STRING-LITERAL-CHAR-EQUIV-OF-STRING-LITERAL-CHAR-FIX-2-FORWARD)
(JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X
 (13
   9
   (:REWRITE JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P))
 (7 5
    (:REWRITE JAVA::ESCAPE-SEQUENCE-FIX-WHEN-ESCAPE-SEQUENCE-P))
 (4 4
    (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::ESCAPE-SEQUENCE-P))
 (1 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P)))
(JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)
(JAVA::STRING-LITERAL-CHAR-KIND$INLINE-STRING-LITERAL-CHAR-EQUIV-CONGRUENCE-ON-X)
(JAVA::CONSP-OF-STRING-LITERAL-CHAR-FIX)
(JAVA::TAG-WHEN-STRING-LITERAL-CHAR-P-FORWARD
 (2
  2
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::TAG-OF-STRING-LITERAL-CHAR-FIX)
(JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE
 (33 22
     (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX))
 (2
  2
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::UNICODE-STRINGLIT-CHAR-P-OF-STRING-LITERAL-CHAR-CHAR->GET
 (3
   1
   (:REWRITE JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X
 (25 25
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-FIX$INLINE))
 (25 25
     (:TYPE-PRESCRIPTION JAVA::CONSP-OF-STRING-LITERAL-CHAR-FIX))
 (13 5
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (8
  8
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)
(JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-STRING-LITERAL-CHAR-EQUIV-CONGRUENCE-ON-X)
(JAVA::STRING-LITERAL-CHAR-CHAR->GET-WHEN-WRONG-KIND
 (6
   2
   (:REWRITE JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P))
 (4 4
    (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-P))
 (2
  2
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR)
(JAVA::RETURN-TYPE-OF-STRING-LITERAL-CHAR-CHAR
 (3
   1
   (:REWRITE JAVA::UNICODE-STRINGLIT-CHAR-FIX-WHEN-UNICODE-STRINGLIT-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR->GET-OF-STRING-LITERAL-CHAR-CHAR
 (71 58
     (:TYPE-PRESCRIPTION JAVA::UNICODE-STRINGLIT-CHAR-FIX))
 (13 13
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-CHAR))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR-OF-FIELDS
 (3
  3
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-FIX-WHEN-CHAR
 (3
  3
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::EQUAL-OF-STRING-LITERAL-CHAR-CHAR
 (9
  9
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (6
  6
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-CHAR-OF-UNICODE-STRINGLIT-CHAR-FIX-GET)
(JAVA::STRING-LITERAL-CHAR-CHAR-OF-UNICODE-STRINGLIT-CHAR-FIX-GET-NORMALIZE-CONST)
(JAVA::STRING-LITERAL-CHAR-CHAR-UNICODE-STRINGLIT-CHAR-EQUIV-CONGRUENCE-ON-GET)
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE
 (2
  2
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::ESCAPE-SEQUENCE-P-OF-STRING-LITERAL-CHAR-ESCAPE->GET
 (3 1
    (:REWRITE JAVA::ESCAPE-SEQUENCE-FIX-WHEN-ESCAPE-SEQUENCE-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X
 (12 4
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (7
  7
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-STRING-LITERAL-CHAR-EQUIV-CONGRUENCE-ON-X)
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET-WHEN-WRONG-KIND
 (6 2
    (:REWRITE JAVA::ESCAPE-SEQUENCE-FIX-WHEN-ESCAPE-SEQUENCE-P))
 (4 4
    (:TYPE-PRESCRIPTION JAVA::ESCAPE-SEQUENCE-P))
 (2
  2
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE)
(JAVA::RETURN-TYPE-OF-STRING-LITERAL-CHAR-ESCAPE
 (3 1
    (:REWRITE JAVA::ESCAPE-SEQUENCE-FIX-WHEN-ESCAPE-SEQUENCE-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::ESCAPE-SEQUENCE-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE->GET-OF-STRING-LITERAL-CHAR-ESCAPE
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE-OF-FIELDS
 (3
  3
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-FIX-WHEN-ESCAPE
 (3
  3
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::EQUAL-OF-STRING-LITERAL-CHAR-ESCAPE
 (4
  4
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (4
  4
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERAL-CHAR-ESCAPE-OF-ESCAPE-SEQUENCE-FIX-GET)
(JAVA::STRING-LITERAL-CHAR-ESCAPE-OF-ESCAPE-SEQUENCE-FIX-GET-NORMALIZE-CONST)
(JAVA::STRING-LITERAL-CHAR-ESCAPE-ESCAPE-SEQUENCE-EQUIV-CONGRUENCE-ON-GET)
(JAVA::STRING-LITERAL-CHAR-FIX-REDEF
 (9 3
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (6 6
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-KIND$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE-OF-ESCAPE-SEQUENCE-FIX-GET-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-ESCAPE->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR-OF-UNICODE-STRINGLIT-CHAR-FIX-GET-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   JAVA::STRING-LITERAL-CHAR-CHAR->GET$INLINE-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST)))
(JAVA::STRING-LITERALP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(JAVA::STRING-LITERALP-OF-CONS)
(JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP)
(JAVA::STRING-LITERALP-WHEN-NOT-CONSP)
(JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP)
(JAVA::TRUE-LISTP-WHEN-STRING-LITERALP)
(JAVA::STRING-LITERALP-OF-LIST-FIX)
(JAVA::STRING-LITERALP-OF-SFIX)
(JAVA::STRING-LITERALP-OF-INSERT)
(JAVA::STRING-LITERALP-OF-DELETE)
(JAVA::STRING-LITERALP-OF-MERGESORT)
(JAVA::STRING-LITERALP-OF-UNION)
(JAVA::STRING-LITERALP-OF-INTERSECT-1)
(JAVA::STRING-LITERALP-OF-INTERSECT-2)
(JAVA::STRING-LITERALP-OF-DIFFERENCE)
(JAVA::STRING-LITERALP-OF-DUPLICATED-MEMBERS)
(JAVA::STRING-LITERALP-OF-REV)
(JAVA::STRING-LITERALP-OF-APPEND)
(JAVA::STRING-LITERALP-OF-RCONS)
(JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP)
(JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL)
(JAVA::STRING-LITERALP-OF-SET-DIFFERENCE-EQUAL)
(JAVA::STRING-LITERALP-OF-INTERSECTION-EQUAL-1)
(JAVA::STRING-LITERALP-OF-INTERSECTION-EQUAL-2)
(JAVA::STRING-LITERALP-OF-UNION-EQUAL)
(JAVA::STRING-LITERALP-OF-TAKE)
(JAVA::STRING-LITERALP-OF-REPEAT)
(JAVA::STRING-LITERAL-CHAR-P-OF-NTH-WHEN-STRING-LITERALP)
(JAVA::STRING-LITERALP-OF-UPDATE-NTH)
(JAVA::STRING-LITERALP-OF-BUTLAST)
(JAVA::STRING-LITERALP-OF-NTHCDR)
(JAVA::STRING-LITERALP-OF-LAST)
(JAVA::STRING-LITERALP-OF-REMOVE)
(JAVA::STRING-LITERALP-OF-REVAPPEND)
(JAVA::STRING-LITERAL-FIX$INLINE)
(JAVA::STRING-LITERALP-OF-STRING-LITERAL-FIX
  (30 1
      (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
  (22 2
      (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
  (18 10
      (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
  (15 1 (:DEFINITION JAVA::STRING-LITERALP))
  (12 6
      (:REWRITE
           JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
  (9 5
     (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
  (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
  (4 4
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
  (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
  (2 2
     (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
  (2 1
     (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP)))
(JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP
   (32 4
       (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
   (28 24
       (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
   (13 3
       (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
   (9 6
      (:REWRITE
           JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
   (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
   (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
   (1 1
      (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS)))
(JAVA::STRING-LITERAL-FIX$INLINE
  (8 8
     (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
  (6 1
     (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
  (6 1
     (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
  (4 4
     (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
  (2 2
     (:REWRITE
          JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (2 2
        (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
     (1 1
        (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP)))
(JAVA::STRING-LITERAL-EQUIV$INLINE)
(JAVA::STRING-LITERAL-EQUIV-IS-AN-EQUIVALENCE)
(JAVA::STRING-LITERAL-EQUIV-IMPLIES-EQUAL-STRING-LITERAL-FIX-1)
(JAVA::STRING-LITERAL-FIX-UNDER-STRING-LITERAL-EQUIV)
(JAVA::EQUAL-OF-STRING-LITERAL-FIX-1-FORWARD-TO-STRING-LITERAL-EQUIV)
(JAVA::EQUAL-OF-STRING-LITERAL-FIX-2-FORWARD-TO-STRING-LITERAL-EQUIV)
(JAVA::STRING-LITERAL-EQUIV-OF-STRING-LITERAL-FIX-1-FORWARD)
(JAVA::STRING-LITERAL-EQUIV-OF-STRING-LITERAL-FIX-2-FORWARD)
(JAVA::CAR-OF-STRING-LITERAL-FIX-X-UNDER-STRING-LITERAL-CHAR-EQUIV
   (33 3
       (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
   (18 3
       (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
   (18 2
       (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
   (12 12
       (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
   (12 12
       (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
   (6 6
      (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
   (6 6
      (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
   (6 6
      (:REWRITE
           JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
   (6 1
      (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
   (3 3
      (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-FIX$INLINE)))
(JAVA::CAR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-CHAR-EQUIV)
(JAVA::CAR-STRING-LITERAL-EQUIV-CONGRUENCE-ON-X-UNDER-STRING-LITERAL-CHAR-EQUIV)
(JAVA::CDR-OF-STRING-LITERAL-FIX-X-UNDER-STRING-LITERAL-EQUIV
  (41 3
      (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
  (22 2
      (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
  (20 20
      (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
  (12 2
      (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
  (4 4
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
  (4 4
     (:REWRITE
          JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP)))
(JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CDR-STRING-LITERAL-EQUIV-CONGRUENCE-ON-X-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CONS-OF-STRING-LITERAL-CHAR-FIX-X-UNDER-STRING-LITERAL-EQUIV
 (34 4
     (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (17 2
     (:REWRITE JAVA::STRING-LITERALP-OF-CONS))
 (10 10
     (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (8 8
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (6 6
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (5 5
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (2
  2
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)))
(JAVA::CONS-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CONS-STRING-LITERAL-CHAR-EQUIV-CONGRUENCE-ON-X-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CONS-OF-STRING-LITERAL-FIX-Y-UNDER-STRING-LITERAL-EQUIV
 (20 2
     (:REWRITE JAVA::STRING-LITERALP-OF-CONS))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (8 8
    (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (8 8
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (6 2
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (5 4
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (2
  2
  (:REWRITE
   JAVA::CONS-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (2
  2
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)))
(JAVA::CONS-OF-STRING-LITERAL-FIX-Y-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CONS-STRING-LITERAL-EQUIV-CONGRUENCE-ON-Y-UNDER-STRING-LITERAL-EQUIV)
(JAVA::CONSP-OF-STRING-LITERAL-FIX
 (18 2
     (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (11 1
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (8 8
    (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (6 1
    (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
 (6 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
 (4 4
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (2 2
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (1
  1
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)))
(JAVA::STRING-LITERAL-FIX-UNDER-IFF
 (18 2
     (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (11 1
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (8 8
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (8 8
    (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (6 1
    (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
 (6 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
 (4 4
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (2 2
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (1
  1
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)))
(JAVA::STRING-LITERAL-FIX-OF-CONS
 (21 3
     (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (9 1
    (:REWRITE JAVA::STRING-LITERALP-OF-CONS))
 (6 6
    (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (6 2
    (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (4 4
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (4 4
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (4 4
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (3 3
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (1
  1
  (:REWRITE
   JAVA::CONS-OF-STRING-LITERAL-FIX-Y-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1
  1
  (:REWRITE
   JAVA::CONS-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1
  1
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV)))
(JAVA::LEN-OF-STRING-LITERAL-FIX
 (35 4
     (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (14 14
     (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (13 13
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (12 2
     (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
 (11 1
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (7 7
    (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (6 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (2 2
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (2
  2
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN)))
(JAVA::STRING-LITERAL-FIX-OF-APPEND
 (114 10
      (:REWRITE JAVA::STRING-LITERAL-FIX-WHEN-STRING-LITERALP))
 (58 2
     (:REWRITE JAVA::STRING-LITERALP-OF-APPEND))
 (40 36
     (:REWRITE JAVA::STRING-LITERALP-WHEN-SUBSETP-EQUAL))
 (29 29
     (:TYPE-PRESCRIPTION JAVA::STRING-LITERALP))
 (24 2
     (:REWRITE JAVA::STRING-LITERALP-OF-LIST-FIX))
 (22 16
     (:REWRITE JAVA::STRING-LITERALP-WHEN-NOT-CONSP))
 (14 4
     (:REWRITE JAVA::STRING-LITERALP-OF-CDR-WHEN-STRING-LITERALP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (12 2
     (:REWRITE JAVA::STRING-LITERAL-CHAR-FIX-WHEN-STRING-LITERAL-CHAR-P))
 (6 1
    (:REWRITE JAVA::STRING-LITERAL-CHAR-P-OF-CAR-WHEN-STRING-LITERALP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2
    (:TYPE-PRESCRIPTION JAVA::STRING-LITERAL-CHAR-P))
 (2 2
    (:REWRITE
         JAVA::STRING-LITERAL-CHAR-P-WHEN-MEMBER-EQUAL-OF-STRING-LITERALP))
 (2
  2
  (:REWRITE
   JAVA::CDR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1
  1
  (:REWRITE
   JAVA::CONS-OF-STRING-LITERAL-FIX-Y-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1
  1
  (:REWRITE
   JAVA::CONS-OF-STRING-LITERAL-CHAR-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-EQUIV))
 (1
  1
  (:REWRITE
   JAVA::CAR-OF-STRING-LITERAL-FIX-X-NORMALIZE-CONST-UNDER-STRING-LITERAL-CHAR-EQUIV)))