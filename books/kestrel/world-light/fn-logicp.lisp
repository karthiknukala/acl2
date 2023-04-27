; A lightweight utility to test whether a function is in :logic mode
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Given a function, FN, in WRLD, determine whether it is in :logic mode.
;; Like logicp but has a stricter guard.
(defund fn-logicp (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld)
                              (function-symbolp fn wrld))))
  (logicp fn wrld))
