; Tests of defstobj+
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defstobj-plus")

;; TODO: Add more tests

(defstobj+ my-stobj
  (my-array-field :type (array integer (10000)) :initially 0)
  )

;; example (lots of theorems generated, since there are quite a few fields)
(defstobj+ my-stobj2
  (my-array1 :type (array integer (10000)) :initially 0)
  ;; resizable:
  (my-array2 :type (array integer (10000)) :resizable t :initially 0)
  ;; predicate is a conjunction:
  (my-array3 :type (array (satisfies natp) (10000)) :resizable t :initially 0)
  ;; predicate is t:
  (my-array4 :type (array t (10000)) :resizable t :initially 0)
  ;; element predicate is a call to satisfies:
  (my-array5 :type (array (satisfies consp) (10000)) :resizable t :initially (a b))
  ;; an element type which NIL satisfies (nicer theorems):
  (my-array6 :type (array (satisfies atom) (10000)) :resizable t :initially nil)
  ;; element predicate is a call to AND:
  (my-array7 :type (array (and integer (satisfies posp)) (10000)) :resizable t :initially 7)

  (my-scalar1 :type integer :initially 0)
  ;; A "scalar" field that is actually a cons ("scalar field" means not an array field, hash table field, etc.):
  (my-scalar2 :type (satisfies consp) :initially (a b))
  ;; predicate is t:
  (my-scalar3 :type t :initially 0)
  ;; a type-spec that is an AND:
  (my-scalar4 :type (and integer (satisfies posp)) :initially 100)
  my-scalar5
  )
