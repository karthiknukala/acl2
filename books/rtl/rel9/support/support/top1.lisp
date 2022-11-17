; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;June, 2001
;;;***************************************************************

(in-package "ACL2")

;the comments represent Eric's best guess as to how to summarize each book

(include-book "util") ;includes the local-defthm macro, etc.
(include-book "ground-zero") ;disables a bunch of functions, includes util
(include-book "rewrite-theory") ; a little utility, which we don't use much...

(include-book "rtl") ;definitions of the RTL primitives
(include-book "rtlarr") ;RTL arrays
(include-book "bvecp-lemmas") ;bvecp lemmas for all(?) of the RTL primitives  (what's the point of this book,
  ;given that we have lib/bvecp-raw-helpers?)

(include-book "bits")
(include-book "bitn")

(include-book "ocat")    ;soon to be removed, since I don't think we use ocat
(include-book "cat-def") ;the definition of cat (since it's a bit complicated).
(include-book "cat")
(include-book "bvecp")
(include-book "ash")
(include-book "decode")
(include-book "encode")
(include-book "mulcat")
(include-book "shft")
(include-book "all-ones")
(include-book "merge2")  ;includes merge
                         ;a mix of lemmas.  eric is sorting these out into appropriate books
                         ;but some lemmas really do mix several functions
(include-book "logior1")
(include-book "setbits")
(include-book "setbitn")

(include-book "float") ;theorems about floating point numbers (factorization into sgn, sig, and expo;
;exactness)
;Eric might want to sort these out into books call sig.lisp, exactp,list, etc.

;floating-point representations:
(include-book "bias") ;Exponent bias for floating point representations.
(include-book "ereps") ;Floating point representations with explicit leading 1 in the mantissa.
(include-book "ireps") ;Floating point representations with implicit leading 1 in the mantissa.

;built-in logical operators:
(include-book "logeqv")
(include-book "logorc1")
(include-book "lognot")
(include-book "logand")
(include-book "logior")
(include-book "logxor")

(include-book "log") ;theorems mixing logical operators with bits and bitn, etc.  some junk in here to sort
  ;out?
  ;figure out the difference between this and merge?

;new logical operators:
(include-book "lnot")
(include-book "land0")
(include-book "lior0")
(include-book "lxor0")
(include-book "lextra0")

(include-book "logs") ;other "logical" operators, especially type (bvecp/natp) lemmas

;floating-point rounding:
(include-book "trunc") ;the trunc rounding-mode
(include-book "away") ;the away rounding-mode
(include-book "near") ;the near rounding-mode
(include-book "near+") ;the near+ rounding-mode
(include-book "oddr") ;the odd rounding-mode
(include-book "sticky") ;sticky rounding
(include-book "rnd") ;rnd (our top level rounding function), and the inf and minf rounding modes
(include-book "drnd-original") ;rounding of denormal numbers

(include-book "bits-trunc") ;theorems about how we implement trunc rounding...

;theorems about circuits for addition
(include-book "add3") ;theorems about how we implement addition of (2 or) 3 bit vectors using land0, lior0, and lxor0
(include-book "lop1") ;leading-one prediction
(include-book "lop2") ;leading-one prediction
(include-book "lop3") ;leading-one prediction
(include-book "stick") ;Some special-purpose lemmas by Russinoff, probably about sticky bit computation

;helpers
(include-book "bvecp-helpers")
(include-book "model-helpers") ; do we use this?
(include-book "rom-helpers")
(include-book "simple-loop-helpers")
;BOZO consider moving lib/simplify-model-helpers to support/ of (better yet), move all the helpers books to lib/

(include-book "clocks")
(include-book "openers")
(include-book "package-defs")
(include-book "simplify-model-helpers")

(include-book "../../arithmetic/top")
(include-book "../../arithmetic/fp")

(include-book "fadd")

; The following form evaluates to (prints out) the list of runes shown below,
; in the environment created by starting up ACL2 and then executing
; (include-book "../lib/top") when ../lib/top was built on top of
; ../support/top1.

#|
; Here is the correct result, which however is more verbose than necessary.
(let ((world (w state)))
  (union-theories
   ;; non-built-in rules
   (set-difference-theories (current-theory :here)
                            (universal-theory 'ground-zero))
   ;; built-in rules
   (intersection-theories (current-theory :here)
                          (universal-theory 'ground-zero))))

But note that:
(let* ((world (w state))
       (cgz (current-theory 'ground-zero))
       (ugz (universal-theory 'ground-zero))
       (here (current-theory :here)))
  (equal (intersection-theories here ugz)
         (union-theories (set-difference-theories
                          cgz
                          (set-difference-theories cgz here))
                         (intersection-theories (set-difference-theories ugz
                                                                         cgz)
                                                here))))

And the following are small:

(let* ((world (w state))
       (cgz (current-theory 'ground-zero))
       (here (current-theory :here)))
  (set-difference-theories cgz here))

(let* ((world (w state))
       (cgz (current-theory 'ground-zero))
       (ugz (universal-theory 'ground-zero))
       (here (current-theory :here)))
  (intersection-theories (set-difference-theories ugz cgz)
                         here))

So the correct result is, alteratively:

(let* ((world (w state))
       (cgz (current-theory 'ground-zero))
       (ugz (universal-theory 'ground-zero))
       (here (current-theory :here))
       (small1 (set-difference-theories cgz here))
       (small2 (intersection-theories (set-difference-theories ugz cgz)
                                      here)))
  (union-theories
   ;; non-built-in rules
   (set-difference-theories (current-theory :here)
                            (universal-theory 'ground-zero))
   ;; built-in rules
   (union-theories (set-difference-theories cgz small1)
                   small2)))

|# ; |

; After Version_4.2, changes to defpkg eliminated the creation of rewrite rules
; for hidden defpkgs, e.g., (:REWRITE U-PACKAGE).  We tried replacing the next
; two forms below with more flexible forms (at least, in
; rtl/rel4/support/top.lisp) that are more likely to survive version changes,
; including the one just mentioned; but the theorem bits-guard failed in
; rtl/rel4/support/guards.cert.  So we just comment out the offending rules in
; the first deftheory below.

(deftheory lib-top1-non-built-ins

;(let ((world (w state)))
;  (set-difference-theories (current-theory :here) (universal-theory 'ground-zero)))

  '(
;    (:REWRITE U-PACKAGE)
;    (:REWRITE ACL2-ASG-PACKAGE)
;    (:REWRITE ACL2-AGP-PACKAGE)
;    (:REWRITE ACL2-CRG-PACKAGE)
    (:EXECUTABLE-COUNTERPART FL)
    (:TYPE-PRESCRIPTION FL)
    (:EXECUTABLE-COUNTERPART BITS)
    (:EXECUTABLE-COUNTERPART BITN)
    (:EXECUTABLE-COUNTERPART BINARY-CAT)
    (:DEFINITION FORMAL-+)
    (:EXECUTABLE-COUNTERPART FORMAL-+)
    (:TYPE-PRESCRIPTION FORMAL-+)
    (:DEFINITION CAT-SIZE)
    (:EXECUTABLE-COUNTERPART CAT-SIZE)
    (:TYPE-PRESCRIPTION CAT-SIZE)
    (:INDUCTION CAT-SIZE)
    (:EXECUTABLE-COUNTERPART MULCAT)
    (:EXECUTABLE-COUNTERPART LNOT)
    (:EXECUTABLE-COUNTERPART BINARY-LAND0)
    (:EXECUTABLE-COUNTERPART BINARY-LIOR0)
    (:EXECUTABLE-COUNTERPART BINARY-LXOR0)
    (:DEFINITION SETBITS)
    (:EXECUTABLE-COUNTERPART SETBITS)
    (:TYPE-PRESCRIPTION SETBITS)
    (:EXECUTABLE-COUNTERPART SETBITN)
    (:EXECUTABLE-COUNTERPART LOG=)
    (:EXECUTABLE-COUNTERPART LOG<>)
    (:EXECUTABLE-COUNTERPART LOG<)
    (:EXECUTABLE-COUNTERPART LOG<=)
    (:EXECUTABLE-COUNTERPART LOG>)
    (:EXECUTABLE-COUNTERPART LOG>=)
    (:EXECUTABLE-COUNTERPART COMP2)
    (:TYPE-PRESCRIPTION COMP2)
    (:EXECUTABLE-COUNTERPART COMP2<)
    (:TYPE-PRESCRIPTION COMP2<)
    (:EXECUTABLE-COUNTERPART COMP2<=)
    (:TYPE-PRESCRIPTION COMP2<=)
    (:EXECUTABLE-COUNTERPART COMP2>)
    (:TYPE-PRESCRIPTION COMP2>)
    (:EXECUTABLE-COUNTERPART COMP2>=)
    (:TYPE-PRESCRIPTION COMP2>=)
    (:EXECUTABLE-COUNTERPART LOGAND1)
    (:TYPE-PRESCRIPTION LOGAND1)
    (:EXECUTABLE-COUNTERPART LOGIOR1)
    (:TYPE-PRESCRIPTION LOGIOR1)
    (:EXECUTABLE-COUNTERPART LOGXOR1)
    (:TYPE-PRESCRIPTION LOGXOR1)
    (:EXECUTABLE-COUNTERPART SHFT)
    (:EXECUTABLE-COUNTERPART DECODE)
    (:EXECUTABLE-COUNTERPART ENCODE)
    (:EXECUTABLE-COUNTERPART IF1)
    (:TYPE-PRESCRIPTION IF1)
    (:REWRITE IF1-0)
    (:REWRITE IF1-NON-0)
    (:REWRITE IF1-X-X)
    (:DEFINITION COND1-MACRO)
    (:EXECUTABLE-COUNTERPART COND1-MACRO)
    (:TYPE-PRESCRIPTION COND1-MACRO)
    (:INDUCTION COND1-MACRO)
    (:EXECUTABLE-COUNTERPART NATP1)
    (:TYPE-PRESCRIPTION NATP1)
    (:EXECUTABLE-COUNTERPART BVECP)
    (:TYPE-PRESCRIPTION BVECP)
    (:REWRITE BVECP-IF1)
    (:EXECUTABLE-COUNTERPART MK-BVEC)
    (:TYPE-PRESCRIPTION MK-BVEC)
    (:REWRITE MK-BVEC-IS-BVECP)
    (:REWRITE MK-BVEC-IDENTITY)
    (:REWRITE BVECP-RESET)
    (:FORWARD-CHAINING BVECP-RESET)
    (:TYPE-PRESCRIPTION BVECP-RESET)
    (:REWRITE BVECP-UNKNOWN)
    (:FORWARD-CHAINING BVECP-UNKNOWN)
    (:TYPE-PRESCRIPTION BVECP-UNKNOWN)
    (:EXECUTABLE-COUNTERPART acl2::<<)
    (:TYPE-PRESCRIPTION acl2::<<)
    (:REWRITE acl2::<<-IRREFLEXIVE)
    (:REWRITE acl2::<<-TRANSITIVE)
    (:REWRITE acl2::<<-ASYMMETRIC)
    (:REWRITE acl2::<<-TRICHOTOMY)
    (:REWRITE acl2::<<-IMPLIES-LEXORDER)
    (:DEFINITION RCDP)
    (:EXECUTABLE-COUNTERPART RCDP)
    (:TYPE-PRESCRIPTION RCDP)
    (:INDUCTION RCDP)
    (:REWRITE RCDP-IMPLIES-ALISTP)
    (:DEFINITION IFRP)
    (:EXECUTABLE-COUNTERPART IFRP)
    (:TYPE-PRESCRIPTION IFRP)
    (:INDUCTION IFRP)
    (:DEFINITION ACL2->RCD)
    (:EXECUTABLE-COUNTERPART ACL2->RCD)
    (:TYPE-PRESCRIPTION ACL2->RCD)
    (:DEFINITION RCD->ACL2)
    (:EXECUTABLE-COUNTERPART RCD->ACL2)
    (:TYPE-PRESCRIPTION RCD->ACL2)
    (:DEFINITION AG-AUX)
    (:EXECUTABLE-COUNTERPART AG-AUX)
    (:TYPE-PRESCRIPTION AG-AUX)
    (:INDUCTION AG-AUX)
    (:EXECUTABLE-COUNTERPART AG)
    (:TYPE-PRESCRIPTION AG)
    (:DEFINITION ACONS-IF)
    (:EXECUTABLE-COUNTERPART ACONS-IF)
    (:TYPE-PRESCRIPTION ACONS-IF)
    (:DEFINITION AS-AUX)
    (:EXECUTABLE-COUNTERPART AS-AUX)
    (:TYPE-PRESCRIPTION AS-AUX)
    (:INDUCTION AS-AUX)
    (:EXECUTABLE-COUNTERPART AS)
    (:TYPE-PRESCRIPTION AS)
    (:REWRITE AG-SAME-AS)
    (:REWRITE AG-DIFF-AS)
    (:REWRITE AS-SAME-AG)
    (:REWRITE AS-SAME-AS)
    (:REWRITE AS-DIFF-AS)
    (:REWRITE AG-OF-NIL-IS-DEFAULT)
    (:REWRITE AS-NON-DEFAULT-CANNOT-BE-NIL)
    (:FORWARD-CHAINING NON-NIL-IF-AG-NOT-DEFAULT)
    (:EXECUTABLE-COUNTERPART BV-ARRP)
    (:TYPE-PRESCRIPTION BV-ARRP)
    (:REWRITE AS-MAPS-BV-ARR-TO-BV-ARR)
    (:REWRITE AG-MAPS-BV-ARR-TO-BVECP)
    (:EXECUTABLE-COUNTERPART MK-BVARR)
    (:TYPE-PRESCRIPTION MK-BVARR)
    (:REWRITE MK-BVARR-IS-BV-ARRP)
    (:REWRITE MK-BVARR-IDENTITY)
    (:DEFINITION POSITIVE-INTEGER-LISTP)
    (:EXECUTABLE-COUNTERPART POSITIVE-INTEGER-LISTP)
    (:TYPE-PRESCRIPTION POSITIVE-INTEGER-LISTP)
    (:INDUCTION POSITIVE-INTEGER-LISTP)
    (:REWRITE BV-ARRP-RESET2)
    (:REWRITE BV-ARRP-UNKNOWN2)
    (:REWRITE BV-ARRP-IF1)
    (:EXECUTABLE-COUNTERPART CG)
    (:TYPE-PRESCRIPTION CG)
    (:TYPE-PRESCRIPTION FL-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION CG-INTEGER-TYPE)
    (:REWRITE FL-INTEGERP)
    (:REWRITE CG-INTEGERP)
    (:LINEAR FL-DEF-LINEAR)
    (:LINEAR CG-DEF-LINEAR)
    (:LINEAR FL-MONOTONE-LINEAR)
    (:LINEAR CG-MONOTONE-LINEAR)
    (:LINEAR N<=FL-LINEAR)
    (:LINEAR N>=CG-LINEAR)
    (:REWRITE FL+INT-REWRITE)
    (:REWRITE CG+INT-REWRITE)
    (:REWRITE FL/INT-REWRITE)
    (:REWRITE FL/INT-REWRITE-ALT)
    (:REWRITE CG/INT-REWRITE)
    (:REWRITE CG/INT-REWRITE-ALT)
    (:REWRITE EXPT-2-POSITIVE-RATIONAL-TYPE)
    (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE)
    (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE)
    (:LINEAR EXPT-2-TYPE-LINEAR)
    (:REWRITE ASH-REWRITE)
    (:REWRITE MOD-0)
    (:REWRITE RATIONALP-MOD)
    (:TYPE-PRESCRIPTION RATIONALP-MOD)
    (:REWRITE INTEGERP-MOD)
    (:TYPE-PRESCRIPTION INTEGERP-MOD)
    (:TYPE-PRESCRIPTION NATP-MOD)
    (:LINEAR MOD-BND-1)
    (:LINEAR MOD-BND-2)
    (:REWRITE MOD-MULT)
    (:REWRITE MOD-DIFF)
    (:REWRITE MOD-DOES-NOTHING)
    (:REWRITE MOD-BY-1)
    (:REWRITE MOD-OF-MOD)
    (:REWRITE MOD-PROD)
    (:LINEAR MOD-BND-3)
    (:LINEAR QUOT-BND)
    (:REWRITE MOD-MULT-2)
    (:LINEAR NK>=K-LINEAR)
    (:REWRITE MOD-MULT-2-GEN)
    (:REWRITE MOD-MULT-2-ALT-GEN)
    (:REWRITE MOD-2*M+1-REWRITE)
    (:EXECUTABLE-COUNTERPART FL-HALF)
    (:TYPE-PRESCRIPTION FL-HALF)
    (:FORWARD-CHAINING BVECP-FORWARD)
    (:FORWARD-CHAINING BVECP-1-0)
    (:FORWARD-CHAINING BVECP-0-1)
    (:DEFINITION BITVEC)
    (:EXECUTABLE-COUNTERPART BITVEC)
    (:TYPE-PRESCRIPTION BITVEC)
    (:TYPE-PRESCRIPTION BITN-NONNEGATIVE-INTEGER)
    (:REWRITE BITN-BVECP)
    (:FORWARD-CHAINING BITN-BVECP-FORWARD)
    (:REWRITE BITN-BVECP-1)
    (:REWRITE BITN-BITN-0)
    (:REWRITE BITN-0)
    (:REWRITE BVECP-BITN-0)
    (:TYPE-PRESCRIPTION BITS-NONNEGATIVE-INTEGERP-TYPE)
    (:REWRITE BITS-0)
    (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER)
    (:REWRITE BITS-N-N-REWRITE)
    (:REWRITE BITS-TAIL)
    (:REWRITE BITS-BVECP)
    (:REWRITE BITS-BVECP-SIMPLE)
    (:REWRITE BITS-BVECP-SIMPLE-2)
    (:DEFINITION SUMBITS)
    (:EXECUTABLE-COUNTERPART SUMBITS)
    (:TYPE-PRESCRIPTION SUMBITS)
    (:INDUCTION SUMBITS)
    (:REWRITE BITN-BITS)
    (:REWRITE BITS-BITS)
    (:REWRITE BITS-PLUS-MULT-2)
    (:REWRITE BITS-DROP-FROM-MINUS)
    (:TYPE-PRESCRIPTION CAT-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE CAT-BVECP)
    (:REWRITE CAT-ASSOCIATIVE)
    (:REWRITE CAT-0)
    (:REWRITE CAT-WITH-N-0)
    (:REWRITE CAT-WITH-M-0)
    (:REWRITE BITN-CAT-CONSTANTS)
    (:REWRITE BITS-CAT-CONSTANTS)
    (:REWRITE CAT-BITS-BITS)
    (:REWRITE CAT-BITN-BITS)
    (:REWRITE CAT-BITS-BITN)
    (:REWRITE CAT-BITN-BITN)
    (:TYPE-PRESCRIPTION MULCAT-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE MULCAT-BVECP)
    (:REWRITE MULCAT-1)
    (:REWRITE MULCAT-0)
    (:REWRITE MULCAT-N-1)
    (:REWRITE BITN-MULCAT-1)
    (:REWRITE SETBITN-REWRITE)
    (:TYPE-PRESCRIPTION SETBITN-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE SETBITN-BVECP)
    (:REWRITE BITN-SETBITN)
    (:TYPE-PRESCRIPTION SHFT-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE SHFT-BVECP)
    (:TYPE-PRESCRIPTION LNOT-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LNOT-BVECP)
    (:REWRITE LNOT-LNOT)
    (:TYPE-PRESCRIPTION LAND0-NONNEGATIVE-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION LIOR0-NONNEGATIVE-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION LXOR0-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LAND0-BVECP)
    (:REWRITE LIOR0-BVECP)
    (:REWRITE LXOR0-BVECP)
    (:REWRITE LAND0-X-Y-0)
    (:REWRITE LIOR0-X-Y-0)
    (:REWRITE LXOR0-X-Y-0)
    (:DEFINITION LOGOP-2-INDUCT)
    (:EXECUTABLE-COUNTERPART LOGOP-2-INDUCT)
    (:TYPE-PRESCRIPTION LOGOP-2-INDUCT)
    (:INDUCTION LOGOP-2-INDUCT)
    (:DEFINITION LOGOP-2-N-INDUCT)
    (:EXECUTABLE-COUNTERPART LOGOP-2-N-INDUCT)
    (:TYPE-PRESCRIPTION LOGOP-2-N-INDUCT)
    (:INDUCTION LOGOP-2-N-INDUCT)
    (:DEFINITION LOGOP-3-INDUCT)
    (:EXECUTABLE-COUNTERPART LOGOP-3-INDUCT)
    (:TYPE-PRESCRIPTION LOGOP-3-INDUCT)
    (:INDUCTION LOGOP-3-INDUCT)
    (:REWRITE LAND0-COMMUTATIVE)
    (:REWRITE LIOR0-COMMUTATIVE)
    (:REWRITE LXOR0-COMMUTATIVE)
    (:REWRITE LAND0-ASSOCIATIVE)
    (:REWRITE LIOR0-ASSOCIATIVE)
    (:REWRITE LXOR0-ASSOCIATIVE)
    (:REWRITE LAND0-COMMUTATIVE-2)
    (:REWRITE LIOR0-COMMUTATIVE-2)
    (:REWRITE LXOR0-COMMUTATIVE-2)
    (:REWRITE LAND0-COMBINE-CONSTANTS)
    (:REWRITE LIOR0-COMBINE-CONSTANTS)
    (:REWRITE LXOR0-COMBINE-CONSTANTS)
    (:REWRITE LAND0-SELF)
    (:REWRITE LIOR0-SELF)
    (:REWRITE LXOR0-SELF)
    (:REWRITE LAND0-0)
    (:REWRITE LIOR0-0)
    (:REWRITE LXOR0-0)
    (:REWRITE LAND0-ONES-REWRITE)
    (:REWRITE LIOR0-ONES-REWRITE)
    (:REWRITE LXOR0-ONES-REWRITE)
    (:REWRITE BITS-LAND0)
    (:REWRITE BITN-LAND0)
    (:REWRITE BITS-LIOR0)
    (:REWRITE BITN-LIOR0)
    (:REWRITE BITS-LXOR0)
    (:REWRITE BITN-LXOR0)
    (:REWRITE LAND0-BND)
    (:LINEAR LAND0-BND)
    (:REWRITE LIOR0-BND)
    (:LINEAR LIOR0-BND)
    (:REWRITE LIOR0-BVECP-2)
    (:REWRITE LIOR0-CAT-CONSTANT)
    (:TYPE-PRESCRIPTION LOGAND1-NONNEGATIVE-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION LOGIOR1-NONNEGATIVE-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION LOGXOR1-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOGAND1-BVECP)
    (:REWRITE LOGIOR1-BVECP)
    (:REWRITE LOGXOR1-BVECP)
    (:REWRITE LOG<-BVECP)
    (:TYPE-PRESCRIPTION LOG<-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG<=-BVECP)
    (:TYPE-PRESCRIPTION LOG<=-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG>-BVECP)
    (:TYPE-PRESCRIPTION LOG>-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG>=-BVECP)
    (:TYPE-PRESCRIPTION LOG>=-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG=-BVECP)
    (:TYPE-PRESCRIPTION LOG=-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG=-COMMUTATIVE)
    (:REWRITE LOG<>-BVECP)
    (:TYPE-PRESCRIPTION LOG<>-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE LOG<>-COMMUTATIVE)
    (:REWRITE LOG=-CAT-CONSTANT)
    (:REWRITE ENCODE-BVECP)
    (:TYPE-PRESCRIPTION ENCODE-NONNEGATIVE-INTEGER-TYPE)
    (:TYPE-PRESCRIPTION DECODE-NONNEGATIVE-INTEGER-TYPE)
    (:REWRITE DECODE-BVECP)
    (:EXECUTABLE-COUNTERPART EXPO)
    (:TYPE-PRESCRIPTION EXPO)
    (:EXECUTABLE-COUNTERPART SGN)
    (:TYPE-PRESCRIPTION SGN)
    (:EXECUTABLE-COUNTERPART SIG)
    (:TYPE-PRESCRIPTION SIG)
    (:REWRITE EXPO-2**N)
    (:REWRITE ALREADY-SIG)
    (:REWRITE SIG-SIG)
    (:EXECUTABLE-COUNTERPART EXACTP)
    (:TYPE-PRESCRIPTION EXACTP)
    (:REWRITE EXACTP-MINUS)
    (:REWRITE BVECP-EXACTP)
    (:REWRITE EXACTP-SIG)
    (:DEFINITION FP+)
    (:EXECUTABLE-COUNTERPART FP+)
    (:TYPE-PRESCRIPTION FP+)
    (:TYPE-PRESCRIPTION FP+-POSITIVE)
    (:EXECUTABLE-COUNTERPART BIAS)
    (:TYPE-PRESCRIPTION BIAS)
    (:TYPE-PRESCRIPTION BIAS-NON-NEGATIVE-INTEGERP-TYPE-PRESCRIPTION)
    (:DEFINITION ESGNF)
    (:EXECUTABLE-COUNTERPART ESGNF)
    (:TYPE-PRESCRIPTION ESGNF)
    (:DEFINITION EEXPOF)
    (:EXECUTABLE-COUNTERPART EEXPOF)
    (:TYPE-PRESCRIPTION EEXPOF)
    (:DEFINITION ESIGF)
    (:EXECUTABLE-COUNTERPART ESIGF)
    (:TYPE-PRESCRIPTION ESIGF)
    (:EXECUTABLE-COUNTERPART EREPP)
    (:TYPE-PRESCRIPTION EREPP)
    (:EXECUTABLE-COUNTERPART EENCODINGP)
    (:TYPE-PRESCRIPTION EENCODINGP)
    (:EXECUTABLE-COUNTERPART EENCODE)
    (:TYPE-PRESCRIPTION EENCODE)
    (:EXECUTABLE-COUNTERPART EDECODE)
    (:TYPE-PRESCRIPTION EDECODE)
    (:REWRITE EENCODINGP-NOT-ZERO)
    (:REWRITE EREPP-EDECODE)
    (:REWRITE EENCODINGP-EENCODE)
    (:REWRITE EDECODE-EENCODE)
    (:REWRITE EENCODE-EDECODE)
    (:REWRITE EXPO-EDECODE)
    (:REWRITE SGN-EDECODE)
    (:REWRITE SIG-EDECODE)
    (:DEFINITION REBIAS-EXPO)
    (:EXECUTABLE-COUNTERPART REBIAS-EXPO)
    (:TYPE-PRESCRIPTION REBIAS-EXPO)
    (:REWRITE NATP-REBIAS-UP)
    (:REWRITE NATP-REBIAS-DOWN)
    (:REWRITE BVECP-REBIAS-UP)
    (:REWRITE BVECP-REBIAS-DOWN)
    (:DEFINITION ISGNF)
    (:EXECUTABLE-COUNTERPART ISGNF)
    (:TYPE-PRESCRIPTION ISGNF)
    (:DEFINITION IEXPOF)
    (:EXECUTABLE-COUNTERPART IEXPOF)
    (:TYPE-PRESCRIPTION IEXPOF)
    (:DEFINITION ISIGF)
    (:EXECUTABLE-COUNTERPART ISIGF)
    (:TYPE-PRESCRIPTION ISIGF)
    (:EXECUTABLE-COUNTERPART NREPP)
    (:TYPE-PRESCRIPTION NREPP)
    (:EXECUTABLE-COUNTERPART DREPP)
    (:TYPE-PRESCRIPTION DREPP)
    (:EXECUTABLE-COUNTERPART IREPP)
    (:TYPE-PRESCRIPTION IREPP)
    (:EXECUTABLE-COUNTERPART NENCODINGP)
    (:TYPE-PRESCRIPTION NENCODINGP)
    (:EXECUTABLE-COUNTERPART DENCODINGP)
    (:TYPE-PRESCRIPTION DENCODINGP)
    (:EXECUTABLE-COUNTERPART IENCODINGP)
    (:TYPE-PRESCRIPTION IENCODINGP)
    (:EXECUTABLE-COUNTERPART NENCODE)
    (:TYPE-PRESCRIPTION NENCODE)
    (:EXECUTABLE-COUNTERPART DENCODE)
    (:TYPE-PRESCRIPTION DENCODE)
    (:EXECUTABLE-COUNTERPART IENCODE)
    (:TYPE-PRESCRIPTION IENCODE)
    (:EXECUTABLE-COUNTERPART NDECODE)
    (:TYPE-PRESCRIPTION NDECODE)
    (:EXECUTABLE-COUNTERPART DDECODE)
    (:TYPE-PRESCRIPTION DDECODE)
    (:EXECUTABLE-COUNTERPART IDECODE)
    (:TYPE-PRESCRIPTION IDECODE)
    (:REWRITE SGN-NDECODE)
    (:REWRITE EXPO-NDECODE)
    (:REWRITE SIG-NDECODE)
    (:REWRITE SGN-DDECODE)
    (:REWRITE EXPO-DDECODE)
    (:REWRITE SIG-DDECODE)
    (:REWRITE SGN-IDECODE)
    (:REWRITE EXPO-IDECODE)
    (:REWRITE SIG-IDECODE)
    (:REWRITE DENCODINGP-DENCODE)
    (:REWRITE IENCODINGP-IENCODE)
    (:REWRITE NREPP-NDECODE)
    (:REWRITE DREPP-DDECODE)
    (:REWRITE IREPP-IDECODE)
    (:REWRITE NENCODINGP-NENCODE)
    (:REWRITE NDECODE-NENCODE)
    (:REWRITE DDECODE-DENCODE)
    (:REWRITE IDECODE-IENCODE)
    (:REWRITE NENCODE-NDECODE)
    (:REWRITE DENCODE-DDECODE)
    (:REWRITE IENCODE-IDECODE)
    (:EXECUTABLE-COUNTERPART TRUNC)
    (:TYPE-PRESCRIPTION TRUNC)
    (:REWRITE TRUNC-POSITIVE)
    (:LINEAR TRUNC-POSITIVE)
    (:REWRITE TRUNC-NEGATIVE)
    (:LINEAR TRUNC-NEGATIVE)
    (:REWRITE TRUNC-0)
    (:REWRITE TRUNC-EXACTP-A)
    (:REWRITE EXPO-TRUNC)
    (:EXECUTABLE-COUNTERPART AWAY)
    (:TYPE-PRESCRIPTION AWAY)
    (:REWRITE AWAY-POSITIVE)
    (:LINEAR AWAY-POSITIVE)
    (:REWRITE AWAY-NEGATIVE)
    (:LINEAR AWAY-NEGATIVE)
    (:REWRITE AWAY-0)
    (:REWRITE AWAY-EXACTP-A)
    (:DEFINITION RE)
    (:EXECUTABLE-COUNTERPART RE)
    (:TYPE-PRESCRIPTION RE)
    (:EXECUTABLE-COUNTERPART NEAR)
    (:TYPE-PRESCRIPTION NEAR)
    (:TYPE-PRESCRIPTION NEAR-POS)
    (:LINEAR NEAR-POS)
    (:REWRITE NEAR-0)
    (:REWRITE NEAR-EXACTP-A)
    (:REWRITE NEAR-MONOTONE)
    (:EXECUTABLE-COUNTERPART NEAR-WITNESS)
    (:TYPE-PRESCRIPTION NEAR-WITNESS)
    (:EXECUTABLE-COUNTERPART NEAR+)
    (:TYPE-PRESCRIPTION NEAR+)
    (:REWRITE SGN-NEAR+)
    (:LINEAR NEAR+-POS)
    (:LINEAR NEAR+-NEG)
    (:REWRITE NEAR+-0)
    (:REWRITE NEAR+-MONOTONE)
    (:REWRITE NEAR+-EXACTP-A)
    (:REWRITE NEAR+-EXACTP-C)
    (:REWRITE NEAR+-EXACTP-D)
    (:EXECUTABLE-COUNTERPART STICKY)
    (:TYPE-PRESCRIPTION STICKY)
    (:REWRITE STICKY-1)
    (:REWRITE STICKY-0)
    (:EXECUTABLE-COUNTERPART ODDR)
    (:TYPE-PRESCRIPTION ODDR)
    (:REWRITE EXPO-ODDR)
    (:DEFINITION KP)
    (:EXECUTABLE-COUNTERPART KP)
    (:TYPE-PRESCRIPTION KP)
    (:DEFINITION INF)
    (:EXECUTABLE-COUNTERPART INF)
    (:TYPE-PRESCRIPTION INF)
    (:DEFINITION MINF)
    (:EXECUTABLE-COUNTERPART MINF)
    (:TYPE-PRESCRIPTION MINF)
    (:EXECUTABLE-COUNTERPART IEEE-MODE-P)
    (:TYPE-PRESCRIPTION IEEE-MODE-P)
    (:DEFINITION COMMON-ROUNDING-MODE-P)
    (:EXECUTABLE-COUNTERPART COMMON-ROUNDING-MODE-P)
    (:TYPE-PRESCRIPTION COMMON-ROUNDING-MODE-P)
    (:EXECUTABLE-COUNTERPART RND)
    (:TYPE-PRESCRIPTION RND)
    (:TYPE-PRESCRIPTION RATIONALP-RND)
    (:REWRITE RND-NON-POS)
    (:TYPE-PRESCRIPTION RND-NON-POS)
    (:LINEAR RND-NON-POS)
    (:REWRITE RND-NON-NEG)
    (:TYPE-PRESCRIPTION RND-NON-NEG)
    (:LINEAR RND-NON-NEG)
    (:TYPE-PRESCRIPTION RND-POS)
    (:TYPE-PRESCRIPTION RND-NEG)
    (:REWRITE RND-0)
    (:EXECUTABLE-COUNTERPART FLIP)
    (:TYPE-PRESCRIPTION FLIP)
    (:REWRITE IEEE-MODE-P-FLIP)
    (:REWRITE COMMON-ROUNDING-MODE-P-FLIP)
    (:REWRITE RND-EXACTP-A)
    (:REWRITE RND-EXACTP-B)
    (:REWRITE EXACTP-RND)
    (:DEFINITION RND-CONST)
    (:EXECUTABLE-COUNTERPART RND-CONST)
    (:TYPE-PRESCRIPTION RND-CONST)
    (:DEFINITION ROUNDUP)
    (:EXECUTABLE-COUNTERPART ROUNDUP)
    (:TYPE-PRESCRIPTION ROUNDUP)
    (:EXECUTABLE-COUNTERPART DRND-ORIGINAL)
    (:TYPE-PRESCRIPTION DRND-ORIGINAL)
    (:REWRITE DRND-ORIGINAL-0)
    (:EXECUTABLE-COUNTERPART SPN)
    (:TYPE-PRESCRIPTION SPN)
    (:LINEAR POSITIVE-SPN)
    (:REWRITE NREPP-SPN)
    (:REWRITE SMALLEST-SPN)
    (:EXECUTABLE-COUNTERPART SPD)
    (:TYPE-PRESCRIPTION SPD)
    (:LINEAR  POSITIVE-SPD)
    (:REWRITE DREPP-SPD)
    (:REWRITE SMALLEST-SPD)
    (:REWRITE DRND-ORIGINAL-OF-DREPP-IS-NOP)
    (:REWRITE DRND-ORIGINAL-SPN-IS-SPN-GENERAL)
    (:REWRITE DRND-ORIGINAL-TRUNC-NEVER-GOES-AWAY-FROM-ZERO)
    (:REWRITE DRND-ORIGINAL-AWAY-NEVER-GOES-TOWARD-ZERO)
    (:REWRITE DRND-ORIGINAL-INF-NEVER-GOES-DOWN)
    (:REWRITE DRND-ORIGINAL-MINF-NEVER-GOES-UP)
    (:REWRITE DRND-ORIGINAL-TRUNC-SKIPS-NO-DENORMALS)
    (:REWRITE DRND-ORIGINAL-AWAY-SKIPS-NO-DENORMALS)
    (:REWRITE DRND-ORIGINAL-INF-SKIPS-NO-DENORMALS)
    (:REWRITE DRND-ORIGINAL-MINF-SKIPS-NO-DENORMALS)
    (:REWRITE DRND-ORIGINAL-DIFF)
    (:EXECUTABLE-COUNTERPART NEXT-DENORMAL)
    (:TYPE-PRESCRIPTION NEXT-DENORMAL)
    (:REWRITE DENORMAL-SPACING)
    (:REWRITE NO-DENORMAL-IS-CLOSER-THAN-WHAT-DRND-ORIGINAL-NEAR-RETURNS)
    (:DEFINITION GEN)
    (:EXECUTABLE-COUNTERPART GEN)
    (:TYPE-PRESCRIPTION GEN)
    (:INDUCTION GEN)
    (:DEFINITION PROP)
    (:EXECUTABLE-COUNTERPART PROP)
    (:TYPE-PRESCRIPTION PROP)
    (:INDUCTION PROP)
    (:REWRITE LAND0-GEN-0)
    (:REWRITE BVECP-1-GEN)
    (:FORWARD-CHAINING BVECP-1-GEN)
    (:REWRITE BVECP-1-PROP)
    (:FORWARD-CHAINING BVECP-1-PROP)
    (:DEFINITION LAMT-0)
    (:EXECUTABLE-COUNTERPART LAMT-0)
    (:TYPE-PRESCRIPTION LAMT-0)
    (:DEFINITION LAMG-0)
    (:EXECUTABLE-COUNTERPART LAMG-0)
    (:TYPE-PRESCRIPTION LAMG-0)
    (:DEFINITION LAMZ-0)
    (:EXECUTABLE-COUNTERPART LAMZ-0)
    (:TYPE-PRESCRIPTION LAMZ-0)
    (:DEFINITION LAM1-0)
    (:EXECUTABLE-COUNTERPART LAM1-0)
    (:TYPE-PRESCRIPTION LAM1-0)
    (:DEFINITION LAM2-0)
    (:EXECUTABLE-COUNTERPART LAM2-0)
    (:TYPE-PRESCRIPTION LAM2-0)
    (:DEFINITION LAM3-0)
    (:EXECUTABLE-COUNTERPART LAM3-0)
    (:TYPE-PRESCRIPTION LAM3-0)
    (:DEFINITION LAM4-0)
    (:EXECUTABLE-COUNTERPART LAM4-0)
    (:TYPE-PRESCRIPTION LAM4-0)
    (:DEFINITION LAM0-0)
    (:EXECUTABLE-COUNTERPART LAM0-0)
    (:TYPE-PRESCRIPTION LAM0-0)
    (:DEFINITION LAMB-0)
    (:EXECUTABLE-COUNTERPART LAMB-0)
    (:TYPE-PRESCRIPTION LAMB-0)
    (:REWRITE A1)
    (:REWRITE A2)
    (:REWRITE A3)
    (:REWRITE A4)
    (:REWRITE A5)
    (:REWRITE A6)
    (:REWRITE A7)
    (:REWRITE A8)
    (:REWRITE A9)
    (:REWRITE A10)
    (:LINEAR A12)
    (:LINEAR A13)
    (:TYPE-PRESCRIPTION A14 . 1)
    (:TYPE-PRESCRIPTION A14 . 2)
    (:REWRITE A15)
    (:REWRITE A16)
    (:FORWARD-CHAINING /-WEAKLY-MONOTONIC)
    (:LINEAR /-WEAKLY-MONOTONIC)
    (:FORWARD-CHAINING /-STRONGLY-MONOTONIC)
    (:LINEAR /-STRONGLY-MONOTONIC)
    (:FORWARD-CHAINING *-WEAKLY-MONOTONIC . 1)
    (:LINEAR *-WEAKLY-MONOTONIC . 1)
    (:FORWARD-CHAINING *-WEAKLY-MONOTONIC . 2)
    (:LINEAR *-WEAKLY-MONOTONIC . 2)
    (:FORWARD-CHAINING *-STRONGLY-MONOTONIC . 1)
    (:LINEAR *-STRONGLY-MONOTONIC . 1)
    (:FORWARD-CHAINING *-STRONGLY-MONOTONIC . 2)
    (:LINEAR *-STRONGLY-MONOTONIC . 2)
    (:FORWARD-CHAINING *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1)
    (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
             . 1)
    (:FORWARD-CHAINING *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2)
    (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
             . 2)
    (:FORWARD-CHAINING *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1)
    (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
             . 1)
    (:FORWARD-CHAINING *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2)
    (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
             . 2)
    (:FORWARD-CHAINING FL-WEAKLY-MONOTONIC . 1)
    (:LINEAR FL-WEAKLY-MONOTONIC . 1)
    (:FORWARD-CHAINING FL-WEAKLY-MONOTONIC . 2)
    (:LINEAR FL-WEAKLY-MONOTONIC . 2)
    (:REWRITE REARRANGE-NEGATIVE-COEFS-<)
    (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL)
    (:REWRITE REARRANGE-FRACTIONAL-COEFS-<)
    (:REWRITE REARRANGE-FRACTIONAL-COEFS-EQUAL)
    (:EXECUTABLE-COUNTERPART POINT-RIGHT-MEASURE)
    (:TYPE-PRESCRIPTION POINT-RIGHT-MEASURE)
    (:EXECUTABLE-COUNTERPART POINT-LEFT-MEASURE)
    (:TYPE-PRESCRIPTION POINT-LEFT-MEASURE)
    (:DEFINITION ACL2::FIRSTN)
    (:EXECUTABLE-COUNTERPART ACL2::FIRSTN)
    (:TYPE-PRESCRIPTION ACL2::FIRSTN)
    (:INDUCTION ACL2::FIRSTN)
    (:DEFINITION ACL2::DROPN)
    (:EXECUTABLE-COUNTERPART ACL2::DROPN)
    (:TYPE-PRESCRIPTION ACL2::DROPN)
    (:INDUCTION ACL2::DROPN)
    (:DEFINITION ACL2::WCMP)
    (:EXECUTABLE-COUNTERPART ACL2::WCMP)
    (:TYPE-PRESCRIPTION ACL2::WCMP)
    (:DEFINITION ACL2::OCMP-AUX)
    (:EXECUTABLE-COUNTERPART ACL2::OCMP-AUX)
    (:TYPE-PRESCRIPTION ACL2::OCMP-AUX)
    (:INDUCTION ACL2::OCMP-AUX)
    (:DEFINITION ACL2::OCMP)
    (:EXECUTABLE-COUNTERPART ACL2::OCMP)
    (:TYPE-PRESCRIPTION ACL2::OCMP)
    (:DEFINITION ACL2::OMEGA-TERM)
    (:EXECUTABLE-COUNTERPART ACL2::OMEGA-TERM)
    (:TYPE-PRESCRIPTION ACL2::OMEGA-TERM)
    (:DEFINITION ACL2::OMEGA)
    (:EXECUTABLE-COUNTERPART ACL2::OMEGA)
    (:TYPE-PRESCRIPTION ACL2::OMEGA)
    (:DEFINITION ACL2::O-MAX)
    (:EXECUTABLE-COUNTERPART ACL2::O-MAX)
    (:TYPE-PRESCRIPTION ACL2::O-MAX)
    (:DEFINITION ACL2::LIMITPART)
    (:EXECUTABLE-COUNTERPART ACL2::LIMITPART)
    (:TYPE-PRESCRIPTION ACL2::LIMITPART)
    (:INDUCTION ACL2::LIMITPART)
    (:DEFINITION ACL2::NATPART)
    (:EXECUTABLE-COUNTERPART ACL2::NATPART)
    (:TYPE-PRESCRIPTION ACL2::NATPART)
    (:INDUCTION ACL2::NATPART)
    (:DEFINITION ACL2::LIMITP)
    (:EXECUTABLE-COUNTERPART ACL2::LIMITP)
    (:TYPE-PRESCRIPTION ACL2::LIMITP)
    (:DEFINITION ACL2::OLEN)
    (:EXECUTABLE-COUNTERPART ACL2::OLEN)
    (:TYPE-PRESCRIPTION ACL2::OLEN)
    (:INDUCTION ACL2::OLEN)
    (:DEFINITION ACL2::O-LAST-EXPT)
    (:EXECUTABLE-COUNTERPART ACL2::O-LAST-EXPT)
    (:TYPE-PRESCRIPTION ACL2::O-LAST-EXPT)
    (:INDUCTION ACL2::O-LAST-EXPT)
    (:DEFINITION ACL2::OB+)
    (:EXECUTABLE-COUNTERPART ACL2::OB+)
    (:TYPE-PRESCRIPTION ACL2::OB+)
    (:INDUCTION ACL2::OB+)
    (:DEFINITION ACL2::O-)
    (:EXECUTABLE-COUNTERPART ACL2::O-)
    (:TYPE-PRESCRIPTION ACL2::O-)
    (:INDUCTION ACL2::O-)
    (:DEFINITION ACL2::COUNT1)
    (:EXECUTABLE-COUNTERPART ACL2::COUNT1)
    (:TYPE-PRESCRIPTION ACL2::COUNT1)
    (:INDUCTION ACL2::COUNT1)
    (:DEFINITION ACL2::COUNT2)
    (:EXECUTABLE-COUNTERPART ACL2::COUNT2)
    (:TYPE-PRESCRIPTION ACL2::COUNT2)
    (:DEFINITION ACL2::PADD)
    (:EXECUTABLE-COUNTERPART ACL2::PADD)
    (:TYPE-PRESCRIPTION ACL2::PADD)
    (:INDUCTION ACL2::PADD)
    (:DEFINITION ACL2::PMULT)
    (:EXECUTABLE-COUNTERPART ACL2::PMULT)
    (:TYPE-PRESCRIPTION ACL2::PMULT)
    (:INDUCTION ACL2::PMULT)
    (:DEFINITION ACL2::OB*)
    (:EXECUTABLE-COUNTERPART ACL2::OB*)
    (:TYPE-PRESCRIPTION ACL2::OB*)
    (:INDUCTION ACL2::OB*)
    (:DEFINITION ACL2::O^1)
    (:EXECUTABLE-COUNTERPART ACL2::O^1)
    (:TYPE-PRESCRIPTION ACL2::O^1)
    (:INDUCTION ACL2::O^1)
    (:DEFINITION ACL2::O^2)
    (:EXECUTABLE-COUNTERPART ACL2::O^2)
    (:TYPE-PRESCRIPTION ACL2::O^2)
    (:DEFINITION ACL2::O^3H)
    (:EXECUTABLE-COUNTERPART ACL2::O^3H)
    (:TYPE-PRESCRIPTION ACL2::O^3H)
    (:INDUCTION ACL2::O^3H)
    (:DEFINITION ACL2::O^3)
    (:EXECUTABLE-COUNTERPART ACL2::O^3)
    (:TYPE-PRESCRIPTION ACL2::O^3)
    (:DEFINITION ACL2::O^4)
    (:EXECUTABLE-COUNTERPART ACL2::O^4)
    (:TYPE-PRESCRIPTION ACL2::O^4)
    (:DEFINITION ACL2::OB^)
    (:EXECUTABLE-COUNTERPART ACL2::OB^)
    (:TYPE-PRESCRIPTION ACL2::OB^)
    (:INDUCTION ACL2::OB^)
    (:DEFINITION E0-ORD-<)
    (:EXECUTABLE-COUNTERPART E0-ORD-<)
    (:TYPE-PRESCRIPTION E0-ORD-<)
    (:INDUCTION E0-ORD-<)
    (:DEFINITION E0-ORDINALP)
    (:EXECUTABLE-COUNTERPART E0-ORDINALP)
    (:TYPE-PRESCRIPTION E0-ORDINALP)
    (:INDUCTION E0-ORDINALP)
    (:DEFINITION ACL2::COPYN)
    (:EXECUTABLE-COUNTERPART ACL2::COPYN)
    (:TYPE-PRESCRIPTION ACL2::COPYN)
    (:INDUCTION ACL2::COPYN)
    (:EXECUTABLE-COUNTERPART ACL2::CTOA)
    (:TYPE-PRESCRIPTION ACL2::CTOA)
    (:REWRITE ACL2::CTOA-<-EQUIV)
    (:FORWARD-CHAINING acl2::|oc.x  <=>  oa(ctoa.x)|)
    (:REWRITE acl2::|oc.x  <=>  oa(ctoa.x)|)
    (:EXECUTABLE-COUNTERPART ACL2::ATOC)
    (:TYPE-PRESCRIPTION ACL2::ATOC)
    (:REWRITE acl2::|oa.x  <=>  oc(atoc.x)|)
    (:REWRITE ACL2::ATOC-<-EQUIV)
    (:WELL-FOUNDED-RELATION ACL2::E0-ORDINAL-WELL-FOUNDED-CNF)
    (:REWRITE RECURSION-BY-POINT-RIGHT)
    (:REWRITE RECURSION-BY-POINT-LEFT)
    (:DEFINITION SUB1-INDUCTION)
    (:EXECUTABLE-COUNTERPART SUB1-INDUCTION)
    (:TYPE-PRESCRIPTION SUB1-INDUCTION)
    (:INDUCTION SUB1-INDUCTION)
    (:DEFINITION SPLIT-LIST)
    (:EXECUTABLE-COUNTERPART SPLIT-LIST)
    (:TYPE-PRESCRIPTION SPLIT-LIST)
    (:INDUCTION SPLIT-LIST)))

(deftheory lib-top1-built-ins-helper-1

; (let* ((world (w state))
;        (cgz (current-theory 'ground-zero))
;        (here (current-theory :here)))
;   (set-difference-theories cgz here)))

  '((:DEFINITION FLOOR)
    (:REWRITE INVERSE-OF-*)
    (:DEFINITION TRUNCATE)
    (:DEFINITION MOD)
    (:DEFINITION REM)
    (:DEFINITION LOGNOT)
    (:DEFINITION EXPT)
    (:INDUCTION EXPT)
    (:DEFINITION ASH)
    (:DEFINITION AREF1)
    (:DEFINITION ASET1)
    (:DEFINITION AREF2)
    (:DEFINITION ASET2)
    (:DEFINITION ACL2::BINARY-LOGAND)
    (:INDUCTION ACL2::BINARY-LOGAND)
    (:DEFINITION ACL2::BINARY-LOGIOR)
    (:DEFINITION LOGORC1)
    (:DEFINITION ACL2::BINARY-LOGEQV)
    (:DEFINITION ACL2::BINARY-LOGXOR)))

(deftheory lib-top1-built-ins-helper-2

; (let* ((world (w state))
;        (cgz (current-theory 'ground-zero))
;        (ugz (universal-theory 'ground-zero))
;        (here (current-theory :here)))
;   (intersection-theories (set-difference-theories ugz cgz)
;                          here))

  nil)

(deftheory lib-top1
  (union-theories
   (theory 'lib-top1-non-built-ins)
   (union-theories (set-difference-theories
                    (current-theory 'ground-zero)
                    (theory 'lib-top1-built-ins-helper-1))
                   (theory 'lib-top1-built-ins-helper-2))))
