; Rules to convert bitops operations to operations from the Kestrel BV library
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/bitops/part-install" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(include-book "kestrel/bv/getbit-def" :dir :system)
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(in-theory (disable bitops::part-select-width-low
                    bitops::part-install-width-low))

;move or make local
(defthm <=-of-*-same-linear-special
  (implies (and (<= 1 y)
                (<= 0 x)
                (rationalp x)
                (rationalp y))
           (<= x (* x y)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance acl2::<=-of-*-and-*-same-forward-1 (x1 1) (x2 y) (y x))
           :in-theory (disable acl2::<=-of-*-and-*-same-forward-1))))

;; (defthm cancel-two
;;   (equal (< (+ y x) x)
;;          (< y 0)))

;; ;gen
;; (defthm <-of-*-cancel-1
;;   (implies (and (posp a)
;;                 (posp b))
;;            (equal (< (* a b) a)
;;                   (< b 1))))

;gen
;; (defthm <-of-*-cancel-2
;;   (implies (and (posp a)
;;                 (posp b)
;;                 (posp c))
;;            (equal (< (* a b) (* c a))
;;                   (< b c))))

(defthm slice-mask
  (implies (and (natp low)
                (natp width))
           (equal (acl2::SLICE (+ -1 LOW WIDTH)
                         LOW
                         (+ (- (EXPT 2 LOW))
                            (* (EXPT 2 LOW) (EXPT 2 WIDTH))))
                  (+ -1 (expt 2 width))))
  :hints (("Goal" :in-theory (e/d (acl2::slice) (ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;; ;;move
;; (defthm <-of-expt-and-expt
;;   (implies (and (natp i)
;;                 (Natp j))
;;            (equal (< (EXPT '2 i) (EXPT '2 j))
;;                   (< i j))))

(defthm slice-too-high-lemma-2
  (implies (and (natp low)
                (natp width)
                (natp size))
           (equal (ACL2::SLICE (+ -1 SIZE)
                               (+ LOW WIDTH)
                               (+ (- (EXPT 2 LOW))
                                  (* (EXPT 2 LOW) (EXPT 2 WIDTH))))
                  0))
  :hints (("Goal" :in-theory (e/d (acl2::slice ACL2::GETBIT-OF-PLUS)
                                  (ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   ACL2::<-OF-BVCHOP-HACK)))))

(defthm part-select-width-low-becomes-slice
  (implies (and (integerp low)
                (integerp width))
           (equal (bitops::part-select-width-low x width low)
                  (acl2::slice (+ low width -1) low x)))
  :hints (("Goal" :in-theory (e/d (bitops::part-select-width-low acl2::slice)
                                  (acl2::bvchop-of-logtail-becomes-slice)))))

(defthmd getbit-of-part-install-width-low-helper
  (implies (and (natp m)
                (natp low)
                (natp width)
;                (integerp x)   ;drop
                )
           (equal (acl2::getbit m (bitops::part-install-width-low val x width low))
                  ;; not simplified; i just want to get rid of the part-install:
                  (acl2::getbit m (acl2::bvcat (- (+ m 1) (+ low width))
                                               (acl2::slice m
                                                            (+ low width)
                                                            x)
                                               (+ width low)
                                               (acl2::bvcat width
                                                            val
                                                            low
                                                            x)))))

  :hints (("Goal" :cases ((NATP (+ 1 (- LOW) M)))
           :in-theory (e/d (bitops::part-install-width-low ifix acl2::getbit-of-logand)
                           (ash logmask)))))

(defthm getbit-of-part-install-width-low
  (implies (and (natp m)
                (natp low)
                (natp width))
           (equal (acl2::getbit m (bitops::part-install-width-low val x width low))
                  ;; not simplified; i just want to get rid of the part-install:
                  (acl2::getbit m (acl2::bvcat (- (+ m 1) (+ low width))
                                               (acl2::slice m
                                                            (+ low width)
                                                            x)
                                               (+ width low)
                                               (acl2::bvcat width
                                                            val
                                                            low
                                                            x)))))
  :hints (("Goal" :use (:instance getbit-of-part-install-width-low-helper (x (ifix x)))
           :in-theory (disable BITOPS::PART-INSTALL-WIDTH-LOW$INLINE))))

;; Unfortunately, PART-INSTALL-WIDTH-LOW does not indicate any size for X.
(defthm part-install-width-low-becomes-bvcat
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free var
                (natp xsize) ;(posp xsize)              ;drop?
                ;(< (+ width low) xsize)   ;allow = ?
                (natp low)
                (natp width))
           (equal (BITOPS::PART-INSTALL-WIDTH-LOW val x width low)
                  (acl2::bvcat (max xsize (+ width low)) ;(- xsize (+ width low))
                               (acl2::slice (+ -1 xsize) (+ low width) x)
                               (+ width low)
                               (acl2::bvcat width val low x))))
  :hints (("Goal" :in-theory (e/d (BITOPS::PART-INSTALL-WIDTH-LOW ACL2::BVCAT-EQUAL-REWRITE
                                                                  ACL2::SLICE-TOO-HIGH-IS-0-NEW
                                                                  acl2::bvnot-of-0
                                                                  acl2::bvuminus-of-1-arg2
                                                                  ;ACL2::BVNOT-TRIM-ALL
                                                                  ACL2::SLICE-TOO-HIGH-IS-0-NEW
                                                                  acl2::expt-of-+
                                                                  ACL2::BVCHOP-OF-LOGNOT-BECOMES-BVNOT
                                                                  ACL2::LOGAND-BECOMES-BVAND
                                                                  ACL2::LOGAND-BECOMES-BVAND-alt)
                                  (;ACL2::EXPONENTS-ADD
                                   ;ACL2::SLICE-OF-+
                                   ;ACL2::BVCAT-OF-+-HIGH   ;looped
                                   ;acl2::BVAND-OF-+-ARG3 ;looped (we should treat a mask of 2^n-1 differently from a generic +
                                   ;ACL2::BVCAT-OF-+-LOW
                                   )))))

(defthm bvchop-of-part-install-width-low-becomes-bvcat
  (implies (and (<= (+ low width) size)
                (natp low)
                (natp width)
                (natp size))
           (equal (acl2::bvchop size (bitops::part-install-width-low val x width low))
                  (acl2::bvcat (- size (+ width low))
                               (acl2::slice (+ -1 size) (+ width low) x)
                               (+ width low)
                               (acl2::bvcat width val low x))))
  :hints (("Goal" :cases ((equal size (+ low width)))
           :in-theory (e/d (bitops::part-install-width-low
                            ACL2::REPEATBIT-OF-1-ARG2
                            acl2::BVNOT-OF-0
                            ACL2::LOGAND-BECOMES-BVAND
                            ACL2::BVCHOP-OF-LOGNOT-BECOMES-BVNOT)
                           ( ;ACL2::SLICE-OF-BVAND
                            ;ACL2::BVCAT-OF-+-HIGH
                            ;;ACL2::EXPONENTS-ADD
                            ;ACL2::BVCAT-OF-+-LOW         ;looped
                            ;acl2::SLICE-OF-+             ;looped
                            ;acl2::BVAND-OF-+-ARG3        ;looped
                            )))))

;replace part-install-width-low with bvcat when inside a slice
;slow proof?
(defthm slice-of-part-install-width-low
  (implies (and (<= (+ low2 width) (+ high 1))
                (natp low)
                (natp high)
                (natp low2)
                (natp width))
           (equal (acl2::slice high low (bitops::part-install-width-low val x width low2))
                  ;;could further simplify this...:
                  (acl2::slice high low (acl2::bvcat (- (+ 1 high) (+ width low2))
                                                     (acl2::slice high (+ width low2) x)
                                                     (+ width low2)
                                                     (acl2::bvcat width val low2 x)))))
  :hints (("Goal" :in-theory (e/d (acl2::slice
                                   ACL2::BVCHOP-OF-LOGTAIL)
                                  (ACL2::SLICE-OF-BVAND
                                   ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   ;;for speed:
                                   ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS
                                   ;ACL2::UNSIGNED-BYTE-P-PLUS
                                   ;ACL2::UNSIGNED-BYTE-P-WHEN-ZP-CHEAP
                                   ;ACL2::BOUND-FROM-NATP-FACT ;seems bad?
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT
                                   ACL2::BVCAT-EQUAL-REWRITE
                                   )))))

;this guesses that X fits in 32 bits, which is common when X is (XR :RFLAGS I X86)
(defthm part-install-width-low-becomes-bvcat-32
  (implies (and (unsigned-byte-p 32 x) ;e.g., the flags
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (acl2::bvcat (max 32 (+ width low))
                               (acl2::slice (+ -1 32) (+ low width) x)
                               (+ width low)
                               (acl2::bvcat width val low x)))))
