; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/utilities/omaps/core" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-other-executable-counterpart-rules*
  :short "List of other executable counterpart rules
          for the proofs generated by ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These should be probably re-organized by their purpose
     rather than by their kind (i.e. executable counterparts)."))
  '((:e booleanp)
    (:e len)
    (:e natp)
    (:e omap::in)
    (:e scope-list-fix)
    (:e scope-listp)
    (:e scopep)
    (:e tyname)
    (:e obj-adeclor-none)
    (:e valuep)
    (:e value-list-fix)
    (:e zp)
    (:e <<)))
