; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-type-prescription-rules*
  :short "List of type prescription rules for the proofs generated by ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These should be probably re-organized by their purpose
     rather than by their kind (i.e. type prescriptions).")
   (xdoc::p
    "In the dynamic semantics, the execution of statements and other entities
     returns @(tsee mv) values, which logically satisfy @(tsee consp);
     the negated application of @(tsee consp) to those execution functions
     comes up in certain subgoals,
     so a simple way to discharge those subgoals
     is to use the type prescription rules for those execution functions.")
   (xdoc::p
    "We also need rules about the constructors of C integer values
     and the C functions that represent C operations and conversions,
     including array read operations."))
  '((:t exec-expr-call-or-pure)
    (:t exec-fun)
    (:t exec-stmt)
    (:t exec-block-item)
    (:t exec-block-item-list)
    (:t schar-from-integer)
    (:t uchar-from-integer)
    (:t sshort-from-integer)
    (:t ushort-from-integer)
    (:t sint-from-integer)
    (:t uint-from-integer)
    (:t slong-from-integer)
    (:t ulong-from-integer)
    (:t sllong-from-integer)
    (:t ullong-from-integer)))
