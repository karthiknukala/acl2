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

; Most or all of this was originally written by Eric Smith while an intern at AMD.

(in-package "RTL")

(set-enforce-redundancy t)

(include-book "../../support/support/clocks")

; The analysis of clocks uses some new functions.
;
; First, even and odd are not the same as evenp and oddp.  For one thing, even
; and odd are defined recursively, and I've proved a bunch of nice rules about
; them which we probably want to use and which may not be proved about evenp and
; oddp (and which may be nicer than what is proveable about evenp and oddp).  One
; nice property of even and odd is that each implies integerp.  (By contrast,
; evenp returns t for non-numbers like nil or '(a b).)  So rules which would
; naturally have both the hyp (integerp n) and the hyp (evenp n) now can just
; have (even n).
;
; Second, I also define a function, MOD4. I didn't want to use MOD itself in the
; clocking logic because reasoning about clocks needs to be fast and predictable.
; (I can imagine that we'll have rules about MOD, especially when doing FP
; proofs, which will just get in the way of our reasoning about clocks. We might
; even open up MOD on occasion.)  So, in order to get complete control over the
; rules which fire when we reason about clocks, I introduced MOD4, which we
; expect never to have to open after proving a nice set of rules about it.
;
; Also, theorems about MOD4 may be nicer than their analogs for MOD.  For
; example, MOD4 is always equal to 0, 1, 2, or 3, but (mod #c(0 1) 4) = #c(0 1),
; which isn't even rational.

(defund pedge (x y)
  (declare (xargs :guard (and (member x '(0 1)) (member y '(0 1)))))
  (and (equal x 0)
       (equal y 1)))

(defund nedge (x y)
  (declare (xargs :guard (and (member x '(0 1)) (member y '(0 1)))))
  (and (equal x 1)
       (equal y 0)))

(defmacro posedge (clk)
  `(and (not (zp n))
        (pedge (,clk (1- n)) (,clk n))))

(defmacro negedge (clk)
  `(and (not (zp n))
        (nedge (,clk (1- n)) (,clk n))))

(defthm pedge-known-false-1
  (not (pedge x 0)))

(defthm pedge-known-false-2
  (not (pedge 1 y)))

(defthm nedge-known-false-1
  (not (nedge x 1)))

(defthm nedge-known-false-2
  (not (nedge 0 y)))


; The call (defperiodic NAME TYPE) creates 1) a defun which defines NAME to be
; a periodic signal of the specified TYPE and 2) a bvecp lemma for that defun
; (all periodics have width 1).

; We intend the user to smash certain periodic inputs to his top level module
; and replace their translations with calls to defperiodic.

; Currently we support the following types of periodic signals:

#|

'fast-clock :

 _   _   _   _   _   _   _
| |_| |_| |_| |_| |_| |_| |_|


'slow-clock-one-quantum-wide

 _       _       _       _
| |_____| |_____| |_____| |__


'slow-clock-one-quantum-wide-shifted :

     _       _       _       _
____| |_____| |_____| |_____| |__


'slow-clock-two-quanta-wide :

 ___     ___     ___     ___
|   |___|   |___|   |___|   |___|


'slow-clock-two-quanta-wide-shifted :

     ___     ___     ___
|___|   |___|   |___|   |___|

'always-1 :

  ___________________________
..


|#

; As the need arises, we can easily change defperiodic to add support for more
; types of signal.

; BTW, currently, the definitions generated by defperiodic return unknown
; values (calls to reset) at time 0 (and whenever N is not a natp).  Perhaps
; this is too conservative, and perhaps defining the value at time 0 would
; allow nicer rewrite rules to be proved.

(defconst *defperiodic-types*

; Keep this in sync with the corresponding definition in the compiler.

  '(fast-clock
    slow-clock-one-quantum-wide
    slow-clock-one-quantum-wide-shifted
    slow-clock-two-quanta-wide
    slow-clock-two-quanta-wide-shifted
    always-1))

(defmacro defperiodic (name type)
  (declare (xargs :guard (member-eq type *defperiodic-types*)))
  (list*
   'encapsulate
   nil
   (case type
     (fast-clock
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           (if (even n) 1 0))))
     (slow-clock-one-quantum-wide
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           (if (equal 0 (mod4 n)) 1 0))))
     (slow-clock-one-quantum-wide-shifted
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           (if (equal 2 (mod4 n)) 1 0))))
     (slow-clock-two-quanta-wide
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           (if (or (equal 0 (mod4 n))
                   (equal 1 (mod4 n)))
               1
             0))))
     (slow-clock-two-quanta-wide-shifted
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           (if (or (equal 2 (mod4 n))
                   (equal 3 (mod4 n)))
               1
             0))))
     (always-1
      `(defund ,name (n)
         (if (zp n)
             (reset (quote ,name) 1)
           1)))
     (otherwise (er hard 'defperiodic
                    "Bad type, ~x0, for defperiodic."
                    type)))
   `((defbvecp ,name (n) 1 :hints (("Goal" :in-theory (enable ,name)))))))
