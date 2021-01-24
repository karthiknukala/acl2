; Support for proofs about R1CSes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; Proof support for R1CS proofs -- TODO: Move this material to libraries

(include-book "kestrel/crypto/r1cs/proof-support" :dir :system)
(include-book "kestrel/crypto/r1cs/lift-r1cs/lift-r1cs-new" :dir :system) ;todo: reduce
(include-book "kestrel/crypto/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/utilities/split-list-fast-rules" :dir :system)
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system)

(defthm mod-of-+-of---when-multiple-arg2
  (implies (and (equal 0 (mod y p))
                (integerp y)
                (integerp x)
                (posp p))
           (equal (MOD (+ x (- y)) P)
                  (mod x p)))
  :hints (("Goal" :in-theory (enable ACL2::MOD-SUM-CASES))))

(defthm add-of-bvnot-becomes-add-of-neg
  (implies (and (integerp y)
                (integerp x)
                (posp n)
                (posp p))
           (equal (add x (acl2::bvnot n y) p)
                  (add (+ -1 (expt 2 n)) (add x (neg (acl2::bvchop n y) p) p) p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot acl2::bvchop-of-sum-cases neg add))))

(defthm pfield::add-associative-when-constant
  (implies (syntaxp (quotep pfield::x))
           (equal (add (add pfield::x pfield::y pfield::p)
                       pfield::z pfield::p)
                  (add pfield::x
                       (add pfield::y pfield::z pfield::p)
                       pfield::p)))
  :hints (("Goal" :in-theory (enable add))))

(acl2::add-known-boolean FE-LISTP)
(acl2::add-known-boolean acl2::bit-listp)

(defthm add-of-bvcat-and-add-of-bvcat-combine-interloper
  (implies (and (unsigned-byte-p lowsize lowval)
                (<= lowsize 31)
                (integerp extra)
                (natp highsize)
                )
           (equal (add (acl2::bvcat highsize highval lowsize '0)
                       ;; todo: why does the single bit here intercede?
                       (add (acl2::bvcat 1 bit 31 lowval)
                            extra
                            p)
                       p)
                  (add (acl2::bvcat 1 bit 31 0)
                       (add (acl2::bvcat highsize highval lowsize lowval)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp add acl2::power-of-2p mul neg))))

;drop the other?
;; move the lowval into the 0 in other other bvcat
(defthm add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
  (implies (and (syntaxp (not (quotep lowval))) ;prevent loops (really we just care about 0)
                (unsigned-byte-p lowsize lowval)
                (<= lowsize 31)
                (integerp extra)
                (natp highsize)
                (< lowsize lowsize2) ;todo: think about this, trying to make sure we make progress (we prefer the lowval to be in the first bvcat since there is extra space in the second cat)
                (natp lowsize2))
           (equal (add (acl2::bvcat highsize highval lowsize 0)
                       ;; todo: why does the highval2 here intercede in the blake proof?
                       (add (acl2::bvcat highsize2 highval2 lowsize2 lowval)
                            extra
                            p)
                       p)
                  (add (acl2::bvcat highsize highval lowsize lowval)
                       (add (acl2::bvcat highsize2 highval2 lowsize2 0)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp add acl2::power-of-2p mul neg))))

(defthmd bvcat-of-bitnot-and-bitnot
  (equal (acl2::bvcat '1 (acl2::bitnot x) '1 (acl2::bitnot y))
         (acl2::bvnot 2 (acl2::bvcat 1 x 1 y))))

(defthmd bvcat-of-bvnot-and-bitnot
  (implies (posp size) ;why not 0?
           (equal (acl2::bvcat size (acl2::bvnot size x) 1 (acl2::bitnot y))
                  (acl2::bvnot (+ 1 size) (acl2::bvcat size x 1 y))))
  :hints (("Goal" :in-theory (e/d (acl2::bitnot-becomes-bvnot) (acl2::bvnot-1-becomes-bitnot-better)))))

(defthmd bvcat-of-bitnot-and-bvnot
  (implies (posp size) ;why not 0?
           (equal (acl2::bvcat 1 (acl2::bitnot x) size (acl2::bvnot size y))
                  (acl2::bvnot (+ 1 size) (acl2::bvcat 1 x size y))))
  :hints (("Goal" :in-theory (e/d (acl2::bitnot-becomes-bvnot) (acl2::bvnot-1-becomes-bitnot-better)))))

(defthmd bvcat-of-bvnot-and-bvnot
  (implies (and (posp highsize) ;why not 0?
                (posp lowsize) ;why not 0?
                )
           (equal (acl2::bvcat highsize (acl2::bvnot highsize highval) lowsize (acl2::bvnot lowsize lowval))
                  (acl2::bvnot (+ highsize lowsize) (acl2::bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :in-theory (e/d (acl2::bitnot-becomes-bvnot) (acl2::bvnot-1-becomes-bitnot-better)))))

;; Try these rules after most rules (which have priority 0), since they have free vars:
;; todo: wrap this command into a nice wrapper that prevents accidentally giving the wrong table name:
(table acl2::axe-rule-priorities-table 'pfield::fep-when-fe-listp-and-memberp 1)
(table acl2::axe-rule-priorities-table 'bitp-when-equal-1 1)
(table acl2::axe-rule-priorities-table 'bitp-when-equal-2. 1)
(table acl2::axe-rule-priorities-table 'acl2::bitp-when-bit-listp-and-memberp. 1)

(defthm equal-of-0-and-add-of-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp x)
                (integerp y)
                (integerp z)
                (posp p)
                )
           (equal (EQUAL '0 (ADD x (ADD y (ADD z (NEG w p) p) p) p))
                  (equal w (ADD x (ADD y z p) p))))
; :hints (("Goal" :in-theory (enable add neg)))
  )

(defthm equal-of-0-and-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp x)
                (integerp y)
                (posp p)
                )
           (equal(EQUAL 0 (ADD x (ADD (NEG w p) y p) p))
                 (equal w (ADD x y p)))))

(DEFTHM ACL2::FEP-OF-BVChop
  (IMPLIES (AND (< (EXPT 2 size) P)
                (NATP size)
                (POSP P))
           (FEP (ACL2::BVChop size x)
                P)))

(defthm acl2::getbit-of-0-when-bitp
  (implies (bitp x)
           (equal (acl2::getbit 0 x)
                  x)))

(defthm unsigned-byte-p-of-add
  (implies (and (unsigned-byte-p (+ -1 n) x)
                (unsigned-byte-p (+ -1 n) y)
                (posp p)
                (posp n)
                (< (expt 2 n) p) ; tighten?
                )
           (unsigned-byte-p n (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

;; todo: floating point gadgets?  strings (dan boneh alligator..)

(defthm add-becomes-bvplus-33
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (posp p)
                (< 8589934592 ;;(expt 2 33) ; tighten?
                   p))
           (equal (add x y p)
                  (acl2::bvplus 33 x y)))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS))))

(defthm add-becomes-bvplus-34
  (implies (and (unsigned-byte-p 33 x)
                (unsigned-byte-p 33 y)
                (posp p)
                (< 17179869184 ;;(expt 2 34) ; tighten?
                   p))
           (equal (add x y p)
                  (acl2::bvplus 34 x y)))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS))))

;try the other one first
(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-34 1)

(defthm getbit-of-bvplus-tighten-to-32
  (implies (and (< 32 size) ; prevent loops
                (< n 32)
                (natp n)
                (natp size))
           (equal (acl2::getbit n (acl2::bvplus size x y))
                  (acl2::getbit n (acl2::bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus)
                                  ( ACL2::GETBIT-TRIM)))))

;gen
(defthm slice-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (< high 32)
                (<= low high) ;drop?
                (natp low)
                (natp high)
                (natp n))
           (equal (acl2::slice high low (acl2::bvplus n x y))
                  (acl2::slice high low (acl2::bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus)
                                  (ACL2::GETBIT-TRIM)))))

(defthm bvchop-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (natp n))
           (equal (acl2::bvchop 32 (acl2::bvplus n x y))
                  (acl2::bvchop 32 (acl2::bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus)
                                  (ACL2::GETBIT-TRIM)))))



(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(defthm getbit-of-add-becomes-getbit-of-bvplus-32
  (implies (and (natp n)
                (< n 32)
                (< 34359738368 ;17179869184 ;;(expt 2 34) ; tighten?
                   p)
                (posp p)
                (unsigned-byte-p 34 x) ;gen?
                (unsigned-byte-p 34 y) ; gen?
                )
           (equal (acl2::getbit n (add x y p))
                  (acl2::getbit n (acl2::bvplus 32 x y))))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS unsigned-byte-p))))

(defthm bvplus-of-bvplus-trim-to-32-arg1
  (implies (and (< 32 n)
                (natp n))
           (equal (acl2::bvplus 32 (acl2::bvplus n x y) z)
                  (acl2::bvplus 32 (acl2::bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))

(defthm bvplus-of-bvplus-trim-to-32-arg2
  (implies (and (< 32 n)
                (natp n))
           (equal (acl2::bvplus 32 z (acl2::bvplus n x y))
                  (acl2::bvplus 32 (acl2::bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))


(defthm equal-of-0-and-add-of-neg
  (implies (and (fep x p)
                (fep y p)
                (posp p)
                )
           (equal (EQUAL '0 (ADD (NEG x p) y p))
                  (equal x y))))

(defthm bvcat-of-slice-tighten
  (implies (and (<= highsize (- high low))
                (<= low high)
                (natp highsize)
                (natp low)
                (natp high))
           (equal (acl2::bvcat highsize (acl2::slice high low x) lowsize lowval)
                  (acl2::bvcat highsize (acl2::slice (+ -1 low highsize) low x) lowsize lowval))))

(defthm bvcat-of-bitnot-low
  (implies (and (natp highsize)
                )
           (equal (acl2::bvcat highsize highval 1 (acl2::bitnot lowbit))
                  (acl2::bvxor (+ highsize 1)
                               1
                               (acl2::bvcat highsize highval 1 lowbit)))))

(defthm bvcat-of-bitnot-high
  (implies (and (natp lowsize)
                )
           (equal (acl2::bvcat 1 (acl2::bitnot highval) lowsize lowval)
                  (acl2::bvxor (+ 1 lowsize)
                               (acl2::bvcat 1 1 lowsize 0) ;todo: simplify?
                               (acl2::bvcat 1 highval lowsize lowval)))))

(defthm slice-of-+-of--1-and-expt-same
  (implies (and (natp low)
                (natp high))
           (equal (ACL2::SLICE high low (+ -1 (EXPT 2 low)))
                  0))
  :hints (("Goal" :in-theory (e/d (acl2::slice) (ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm bvcat-of-bvnot-low
  (implies (and (natp highsize)
                (posp lowsize) ;gen
                )
           (equal (acl2::bvcat highsize highval lowsize (acl2::bvnot lowsize lowbit))
                  (acl2::bvxor (+ highsize lowsize)
                               (acl2::bvchop lowsize -1) ;todo: improve?
                               (acl2::bvcat highsize highval lowsize lowbit))))
  :hints (("Goal" :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-bvxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (acl2::bvcat highsize highval lowsize (acl2::bvxor lowsize k lowval))
                  (acl2::bvxor (+ highsize lowsize)
                               (acl2::bvchop lowsize k)
                               (acl2::bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (acl2::bvcat highsize (acl2::bvxor highsize k highval) lowsize lowval)
                  (acl2::bvxor (+ highsize lowsize)
                               (acl2::bvcat highsize k lowsize 0) ;should get computed
                               (acl2::bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize))
           (equal (acl2::bvcat highsize highval 1 (acl2::bitxor k lowval))
                  (acl2::bvxor (+ highsize 1)
                               (acl2::bvchop 1 k)
                               (acl2::bvcat highsize highval 1 lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp lowsize))
           (equal (acl2::bvcat 1 (acl2::bitxor k highval) lowsize lowval)
                  (acl2::bvxor (+ 1 lowsize)
                               (acl2::bvcat 1 k lowsize 0) ;should get computed
                               (acl2::bvcat 1 highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvnot-high
  (implies (and (natp lowsize)
                (natp highsize))
           (equal (acl2::bvcat highsize (acl2::bvnot highsize highval) lowsize lowval)
                  (acl2::bvxor (+ highsize lowsize)
                               (acl2::bvcat highsize (acl2::bvchop highsize -1) lowsize 0) ;todo: simplify?
                               (acl2::bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize))
           :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-slice-same-becomes-rightrotate
  (implies (and (equal upper-bit 31) ;gen!
                (equal upper-bit (+ -1 highsize lowsize))
                (natp highsize)
                (natp lowsize)
                (< lowsize upper-bit)
                (< highsize upper-bit)
                (posp highsize) ;gen
                )
           (equal (ACL2::BVCAT highsize x lowsize (ACL2::SLICE upper-bit highsize x))
                  (acl2::rightrotate (+ 1 upper-bit) highsize x)))
  :hints (("Goal" :in-theory (enable ;ACL2::RIGHTROTATE
                              ))))

(defthm bvcat-of-bitxor-and-bitxor-adjacent-bits
  (implies (and (natp low1)
                (equal high1 (+ 1 low1))
                (natp low2)
                (equal high2 (+ 1 low2)))
           (equal (acl2::bvcat 1 (acl2::bitxor (acl2::getbit high1 x) (acl2::getbit high2 y))
                               1 (acl2::bitxor (acl2::getbit low1 x) (acl2::getbit low2 y)))
                  (acl2::bvxor 2 (acl2::slice high1 low1 x) (acl2::slice high2 low2 y)))))

(defthm bvxor-of-slice-trim
  (implies (and (< n (+ 1 (- high low)))
                (natp n)
                (< low high)
                (natp high)
                (natp low))
           (equal (acl2::bvxor n (acl2::slice high low x) y)
                  (acl2::bvxor n (acl2::slice (+ -1 (+ n low)) low x) y))))

(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (acl2::bvcat 1 (acl2::bitxor (acl2::getbit high1 x) (acl2::getbit high2 y))
                               n (acl2::bvxor n (acl2::slice high1minus1 low1 x) (acl2::slice high2minus1 low2 y)))
                  (acl2::bvxor (+ 1 n)
                               (acl2::slice high1 low1 x) (acl2::slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;; This version commutes the args to the first bitxor
(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (acl2::bvcat 1 (acl2::bitxor (acl2::getbit high2 y) (acl2::getbit high1 x))
                               n (acl2::bvxor n (acl2::slice high1minus1 low1 x) (acl2::slice high2minus1 low2 y)))
                  (acl2::bvxor (+ 1 n)
                               (acl2::slice high1 low1 x) (acl2::slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;; This version commutes the args to the bitxor
(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (acl2::bvcat 1 (acl2::bitxor (acl2::getbit high2 y) (acl2::getbit high1 x))
                               n (acl2::bvxor n (acl2::slice high1minus1 low1 x) (acl2::slice high2minus1 low2 y)))
                  (acl2::bvxor (+ 1 n)
                               (acl2::slice high1 low1 x) (acl2::slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;todo: make an alt version
(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (acl2::bvcat n1 (acl2::bvxor n1 (acl2::slice high1 mid1 x) (acl2::slice high2 mid2 y))
                               n2 (acl2::bvxor n2 (acl2::slice high1minus1 low1 x) (acl2::slice high2minus1 low2 y)))
                  (acl2::bvxor (+ n1 n2)
                               (acl2::slice high1 low1 x) (acl2::slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;; This version commutes the args to the first bvxor
(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (acl2::bvcat n1 (acl2::bvxor n1 (acl2::slice high2 mid2 y) (acl2::slice high1 mid1 x))
                               n2 (acl2::bvxor n2 (acl2::slice high1minus1 low1 x) (acl2::slice high2minus1 low2 y)))
                  (acl2::bvxor (+ n1 n2)
                               (acl2::slice high1 low1 x) (acl2::slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(acl2::defopeners acl2::bits-to-bytes-little)

;rename
(defthmd acl2::bvplus-commutative-increasing-dag
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-increasing-dag 'acl2::bvplus acl2::x acl2::y acl2::dag-array))
           (equal (acl2::bvplus size acl2::x acl2::y)
                  (acl2::bvplus size acl2::y acl2::x))))

;rename
(defthmd acl2::bvplus-commutative-2-increasing-dag
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-increasing-dag 'acl2::bvplus acl2::x acl2::y acl2::dag-array))
           (equal (acl2::bvplus size acl2::x (acl2::bvplus size acl2::y acl2::z))
                  (acl2::bvplus size acl2::y (acl2::bvplus size acl2::x acl2::z)))))


;mostly for axe
(DEFTHMd ACL2::EQUAL-OF-CONS-when-quotep
  (IMPLIES (SYNTAXP (QUOTEP k))
           (EQUAL (EQUAL k (CONS x y))
                  (AND (CONSP k)
                       (EQUAL x (CAR k))
                       (EQUAL y (CDR k))))))

(DEFTHM ACL2::BVCHOP-of-1-when-bitp
  (IMPLIES (bitp x)
           (EQUAL (ACL2::BVCHOP 1 x)
                  x))
  :HINTS (("Goal" :IN-THEORY (ENABLE UNSIGNED-BYTE-P))))

(defthm equal-of-1-and-add-when-bitp-arg1
  (implies (and (bitp x)
                (fep y p)
                (posp p)
                (< 1 p))
           (equal (equal 1 (add x y p))
                  (equal y (acl2::bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

(defthm equal-of-1-and-add-when-bitp-arg2
  (implies (and (bitp x)
                (fep y p)
                (posp p)
                (< 1 p))
           (equal (equal 1 (add y x p))
                  (equal y (acl2::bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

;only needed for axe
(DEFTHMd ACL2::BVCAT-EQUAL-REWRITE-CONSTANT-alt
  (IMPLIES
   (AND (SYNTAXP (QUOTEP ACL2::X))
        (SYNTAXP (QUOTEP ACL2::HIGHSIZE))
        (SYNTAXP (QUOTEP ACL2::LOWSIZE))
        (NATP ACL2::LOWSIZE)
        (NATP ACL2::HIGHSIZE))
   (EQUAL
    (EQUAL (ACL2::BVCAT ACL2::HIGHSIZE ACL2::HIGHVAL
                        ACL2::LOWSIZE ACL2::LOWVAL)
           ACL2::X)
    (AND
     (UNSIGNED-BYTE-P (+ ACL2::LOWSIZE ACL2::HIGHSIZE)
                      ACL2::X)
     (EQUAL (ACL2::BVCHOP ACL2::LOWSIZE ACL2::X)
            (ACL2::BVCHOP ACL2::LOWSIZE ACL2::LOWVAL))
     (EQUAL (ACL2::SLICE (+ -1 ACL2::LOWSIZE ACL2::HIGHSIZE)
                         ACL2::LOWSIZE ACL2::X)
            (ACL2::BVCHOP ACL2::HIGHSIZE ACL2::HIGHVAL))))))

;or just turn equals around?
;only needed for axe
(defthmd acl2::equal-of-cons-when-quotep-alt
  (implies (syntaxp (quotep k))
           (equal (equal (cons x y) k)
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

(defthm bvxor-of-constant-trim-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (integerp size))
           (equal (acl2::bvxor size k x)
                  (acl2::bvxor size (acl2::bvchop size k) x))))

(defthm equal-of-constant-and-add-of-neg
  (implies (and (syntaxp (quotep k))
                (fep k p)
                (fep x p)
                (fep y p)
                (posp p))
           (equal (equal k (add (neg x p) y p))
                  (equal x (add (- k) y p)))))

(defthm equal-of-bitnot-and-bitnot
  (equal (equal (acl2::bitnot x) (acl2::bitnot y))
         (equal (acl2::getbit 0 x) (acl2::getbit 0 y)))
  :hints (("Goal" :in-theory (enable acl2::bitnot))))

;; only for Axe
(defthmd acl2::getbit-trim-dag-all-gen
  (implies (and (<= 0 acl2::n)
                (acl2::axe-syntaxp (acl2::term-should-be-trimmed-axe-plus-one
                                    acl2::n acl2::x 'acl2::all
                                    acl2::dag-array))
                (natp acl2::n))
           (equal (acl2::getbit acl2::n acl2::x)
                  (acl2::getbit acl2::n
                                (acl2::trim (+ 1 acl2::n) acl2::x))))
  :hints (("Goal" :in-theory (enable acl2::trim))))
