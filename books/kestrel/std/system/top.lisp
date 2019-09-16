; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-free-bound-vars")
(include-book "conjoin")
(include-book "function-symbolp")
(include-book "macro-keyword-args")
(include-book "macro-required-args")
(include-book "macro-symbolp")
(include-book "primitivep")
(include-book "rawp")
(include-book "remove-mbe")
(include-book "theorem-symbolp")
(include-book "unquote-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system
  :parents (std-extensions std)
  :short
  (xdoc::topstring
   "A library that complements the "
   (xdoc::seetopic "system-utilities" "built-in system utilities")
   " with theorems and non-built-in system utilities.")
  :long
  (xdoc::topstring
   (xdoc::p
    "These could be moved under @('[books]/std') at some point.")))
