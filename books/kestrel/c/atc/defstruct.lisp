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

(include-book "abstract-syntax")
(include-book "structures")

(include-book "../language/portable-ascii-identifiers")

(include-book "kestrel/fty/pseudo-event-form" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shallow-structures
  :parents (atc-shallow-embedding)
  :short "A model of C structures in the shallow embedding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our initial model of C structures is fairly simple,
     but we will extend it as needed.")
   (xdoc::p
    "Since C structure types are user-defined,
     we provide a macro @(tsee defstruct) to define
     an ACL2 representation of a C structure type.
     The user must call this macro
     to introduce the structure types that the C code must use.")
   (xdoc::p
    "The @(tsee defstruct) macro takes as inputs
     the name (i.e. tag [C:6.7.2.3]) of the structure type
     and a list of members,
     each of which consists of a name and a designation of an integer type
     (for now we only support members of integer types).
     The names of the structure type and of the members
     must be symbols whose @(tsee symbol-name) is a portable ASCII identifier;
     the members have all different @(tsee symbol-name)s
     (it is not enough for the symbols to be distinct).
     The designation of the integer types is one of the symbols")
   (xdoc::ul
    (xdoc::li "@('schar')")
    (xdoc::li "@('uchar')")
    (xdoc::li "@('sshort')")
    (xdoc::li "@('ushort')")
    (xdoc::li "@('sint')")
    (xdoc::li "@('uint')")
    (xdoc::li "@('slong')")
    (xdoc::li "@('ulong')")
    (xdoc::li "@('sllong')")
    (xdoc::li "@('ullong')"))
   (xdoc::p
    "which are the names of the corresponding fixtypes.")
   (xdoc::p
    "The @(tsee defstruct) macro introduces
     a recognizer called @('struct-<tag>-p'),
     where @('<tag>') is the tag of the structure type.
     It also introduces functions to read and write the members,
     called @('struct-<tag>-read-<member>')
     and @('struct-<tag>-write-<member>'),
     where @('<tag>') is the tag and @('<member>') is the member name.")
   (xdoc::p
    "The member readers and writers generated by @(tsee defstruct)
     are analogous to the integer array readers and writers
     in the model of C integer arrays in the shallow embedding.
     A member reader returns the value of the member,
     while a member writer returns an updated structure value.")
   (xdoc::p
    "C code shallowly embedded in ACL2 can use
     the recognizers @('struct-<tag>-p') in guards
     to specify structure types for parameters;
     more precisely, pointers to structure types, initially.
     That is, similarly to arrays, structures are in the heap,
     and pointers to them are passed to the represented C functions,
     which may side-effect those structures via the member writers,
     which represent assignments to structure members
     accessed via the C @('->') operator (not the @('.') operator).
     C structures may also be passed around by value in general,
     but initially we support only passing by pointer.
     Note that C arrays may only be passed by pointers, in effect,
     as arrays are not first-class entities in C,
     but merely collections of contiguous objects,
     normally accessed via pointers to the first object of the collections.")
   (xdoc::p
    "The @(tsee defstruct) macro also records, in an ACL2 table,
     information about the shallowly embedded structures it defines."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defstruct-table*
  :short "Name of the table of shallowly embedded C structures."
  'defstruct-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defstruct-info
  :short "Fixtype of information about shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each C structure type defined via @(tsee defstruct), we store:")
   (xdoc::ul
    (xdoc::li
     "The tag, as an identifier.
      While currently @(tsee ident) is just a wrapper of @(tsee string),
      it may include invariants in the future.
      Thus, having the tag stored as an identifier in the structure information
      will spare us from having to double-check the invariants
      if we were to construct the identifier from the string.")
    (xdoc::li
     "Information for the members (names and types);
      see @(tsee member-type) in the deep embedding.")
    (xdoc::li
     "The recognizer of the structures.")
    (xdoc::li
     "The fixer of the structures.")
    (xdoc::li
     "The readers of (the members of) the structures,
      in the same order as the members.")
    (xdoc::li
     "The writers of (the members of) the structures,
      in the same order as the members.")
    (xdoc::li
     "The name of the theorem that rewrites away the fixer
      when the recognizer holds.")
    (xdoc::li
     "A list of the names of the return type theorems
      for all the member readers,
      in the same order as the members.")
    (xdoc::li
     "A list of the names of the return type theorems
      for all the member writers,
      in the same order as the members.")
    (xdoc::li
     "The name of a theorem asserting that
      if something is a structure of this type
      then it is not an error.")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies @(tsee valuep).")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies that the @(tsee value-kind) is @(':struct').")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies a specific value of @(tsee value-struct->tag).")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies a specific value of
      @(tsee member-values-to-types) of @(tsee value-struct->members)."))
   (xdoc::p
    "The call of @(tsee defstruct).
     This supports redundancy checking."))
  ((tag ident)
   (members member-type-list)
   (recognizer symbolp)
   (fixer symbolp)
   (readers symbol-listp)
   (writers symbol-listp)
   (fixer-recognizer-thm symbolp)
   (reader-return-thms symbol-listp)
   (writer-return-thms symbol-listp)
   (not-error-thm symbolp)
   (valuep-thm symbolp)
   (value-kind-thm symbolp)
   (tag-thm symbolp)
   (members-thm symbolp)
   (call pseudo-event-form))
  :pred defstruct-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption defstruct-info-option
  defstruct-info
  :short "Fixtype of
          optional information about shallowly embedded C structures."
  :pred defstruct-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defstruct-table-definition
  :short "Definition of the table of shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys are strings that are @(tsee symbol-name)s of
     symbols that represent the tags of the structures.
     The name of each such symbol is a portable ASCII C identifiers,
     but this constraint is not enforced in the table's guard.
     The keys in the table are unique.")
   (xdoc::p
    "The values are the information about the structures.
     See @(tsee defstruct-info)."))

  (make-event
   `(table ,*defstruct-table* nil nil
      :guard (and (stringp acl2::key)
                  (defstruct-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-table-lookup ((tag stringp) (wrld plist-worldp))
  :returns (info? defstruct-info-optionp
                  :hints (("Goal" :in-theory (enable defstruct-info-optionp))))
  :short "Retrieve information about a shallowly embedded C structure."
  (b* ((pair (assoc-equal tag (table-alist+ *defstruct-table* wrld)))
       ((when (not (consp pair))) nil)
       (info (cdr pair))
       ((unless (defstruct-infop info))
        (raise "Internal error: malformed DEFSTRUCT information ~x0." info)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-table-record-event ((tag stringp) (info defstruct-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of shallowly embedded C structures
          by recording a new C structure in it."
  `(table ,*defstruct-table* ,tag ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-to-recognizer ((type typep) (wrld plist-worldp))
  :returns (recognizer symbolp)
  :short "ACL2 recognizer corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a pointer to integer type,
     the predicate is the recognizer of arrays with that element type.
     For a pointer to structure type,
     the predicate is the recognizer of structures of that type.
     This is based on our current ACL2 representation of C types,
     which may be extended in the future;
     note that, in the current representation,
     the predicate corresponding to the type
     is not a recognizer of pointer values.
     We return @('nil') for other types."))
  (type-case
   type
   :void nil
   :char nil
   :schar 'scharp
   :uchar 'ucharp
   :sshort 'sshortp
   :ushort 'ushortp
   :sint 'sintp
   :uint 'uintp
   :slong 'slongp
   :ulong 'ulongp
   :sllong 'sllongp
   :ullong 'ullongp
   :struct nil
   :pointer (type-case
             type.to
             :void nil
             :char nil
             :schar 'schar-arrayp
             :uchar 'uchar-arrayp
             :sshort 'sshort-arrayp
             :ushort 'ushort-arrayp
             :sint 'sint-arrayp
             :uint 'uint-arrayp
             :slong 'slong-arrayp
             :ulong 'ulong-arrayp
             :sllong 'sllong-arrayp
             :ullong 'ullong-arrayp
             :struct (b* ((info (defstruct-table-lookup
                                  (ident->name type.to.tag)
                                  wrld))
                          ((unless info)
                           (raise "Internal error: no recognizer for ~x0."
                                  type)))
                       (defstruct-info->recognizer info))
             :pointer nil
             :array nil)
   :array nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-to-fixer ((type typep) (wrld plist-worldp))
  :returns (fixer symbolp)
  :short "ACL2 fixer corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the fixers for
     the predicates returned by @(tsee atc-type-to-recognizer)."))
  (type-case
   type
   :void nil
   :char nil
   :schar 'schar-fix
   :uchar 'uchar-fix
   :sshort 'sshort-fix
   :ushort 'ushort-fix
   :sint 'sint-fix
   :uint 'uint-fix
   :slong 'slong-fix
   :ulong 'ulong-fix
   :sllong 'sllong-fix
   :ullong 'ullong-fix
   :struct nil
   :pointer (type-case
             type.to
             :void nil
             :char nil
             :schar 'schar-array-fix
             :uchar 'uchar-array-fix
             :sshort 'sshort-array-fix
             :ushort 'ushort-array-fix
             :sint 'sint-array-fix
             :uint 'uint-array-fix
             :slong 'slong-array-fix
             :ulong 'ulong-array-fix
             :sllong 'sllong-array-fix
             :ullong 'ullong-array-fix
             :struct (b* ((info (defstruct-table-lookup
                                  (ident->name type.to.tag)
                                  wrld))
                          ((unless info)
                           (raise "Internal error: no fixer for ~x0."
                                  type)))
                       (defstruct-info->fixer info))
             :pointer nil
             :array nil)
   :array nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-process-members ((members true-listp) (ctx ctxp) state)
  :returns (mv erp (meminfos member-type-listp) state)
  :short "Process the member inputs of a @(tsee defstruct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the inputs of @(tsee defstruct) after the first one,
     which specifies the structure tag.
     Each such input must be a doublet consisting of two symbols.
     The first symbol represents the member name:
     the name of the symbol must be a portable ASCII C identifier
     that is distinct from the other member names.
     The second symbol represents the member type:
     it must be one of the fixtype names of the C integer types
     (see @(see shallow-structures))."))
  (b* (((when (endp members)) (acl2::value nil))
       (member (car members))
       ((unless (std::tuplep 2 member))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE), ~
                   but the input ~x0 does not have this form."
                  member))
       (name (first member))
       (type (second member))
       ((unless (symbolp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols, ~
                   but the first component of ~x0 is not a symbol."
                  member))
       (name (symbol-name name))
       ((unless (ident-stringp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols ~
                   where the SYMBOL-NAME of NAME is ~
                   a portable ASCII C identifier (see ATC user documentation), ~
                   but the SYMBOL-NAME of the first component of ~x0 ~
                   is not a portable ASCII C identifier."
                  member))
       ((unless (symbolp type))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols, ~
                   but the second component of ~x0 is not a symbol."
                  member))
       (type (fixtype-to-integer-type type))
       ((when (not type))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols ~
                   where TYPE is one of the symbols in ~&0, ~
                   but the second component of ~x1 ~
                   is not one of those symbols."
                  '(schar
                    uchar
                    sshort
                    ushort
                    sint
                    uint
                    slong
                    ulong
                    sllong
                    ullong)
                  member))
       (meminfo (make-member-type :name (ident name) :type type))
       ((er meminfos) (defstruct-process-members (cdr members) ctx state))
       ((when (member-equal (ident name)
                            (member-type-list->name-list meminfos)))
        (er-soft+ ctx t nil
                  "There are distinct members with the same name ~x0."
                  name)))
    (acl2::value (cons meminfo meminfos)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-process-inputs ((args true-listp)
                                  (call pseudo-event-formp)
                                  (ctx ctxp)
                                  state)
  :returns (mv erp
               (val (tuple (tag symbolp)
                           (tag-ident identp)
                           (members member-type-listp)
                           (redundant booleanp)
                           val))
               state)
  :short "Process the inputs of a @(tsee defstruct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We process the tag and the members.
     If the table already contains an entry for this tag,
     the call must be identical, in which case the call is redundant;
     if the call is not identical, it is an error."))
  (b* ((irrelevant (list nil (irr-ident) nil nil))
       ((unless (consp args))
        (er-soft+ ctx t irrelevant
                  "There must be at least one input, ~
                   but no inputs were supplied."))
       (tag (car args))
       ((unless (symbolp tag))
        (er-soft+ ctx t irrelevant
                  "The first input must be a symbol, ~
                   but ~x0 is not."
                  tag))
       (tag-name (symbol-name tag))
       ((unless (ident-stringp tag-name))
        (er-soft+ ctx t irrelevant
                  "The name ~x0 of the symbol ~x1 passed as first input, ~
                   which defines the name of the structure, ~
                   must be a portable ASCII C identifier."
                  tag-name tag))
       (tag-ident (ident tag-name))
       (info (defstruct-table-lookup tag-name (w state)))
       ((when info)
        (if (equal (defstruct-info->call info) call)
            (acl2::value (list tag (irr-ident) nil t))
          (er-soft+ ctx t irrelevant
                    "There is already a structure with tag ~x0 ~
                     recorded in the table of shallowly embedded C structures, ~
                     but its call ~x1 differs from the current ~x2, ~
                     so the call is not redundant."
                    tag-name (defstruct-info->call info) call)))
       (members (cdr args))
       ((unless (consp members))
        (er-soft+ ctx t irrelevant
                  "There must be at least one member."))
       ((mv erp members state) (defstruct-process-members members ctx state))
       ((when erp) (mv erp irrelevant state)))
    (acl2::value (list tag tag-ident members nil)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defstruct-support-theorems
  :short "Theorems supporting @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The events generated by @(tsee defstruct) include certain theorems
     that are specific to the structure type being defined.
     These theorems are proved from some general theorems given here."))

  (defruled defstruct-reader-lemma
    (implies (equal meminfos (member-values-to-types members))
             (b* ((type (member-type-lookup name meminfos))
                  (val (struct-read-member-aux name members)))
               (implies (typep type)
                        (and (valuep val)
                             (equal (type-of-value val)
                                    type)))))
    :prep-lemmas
    ((defrule lemma
       (b* ((type (member-type-lookup name (member-values-to-types members)))
            (val (struct-read-member-aux name members)))
         (implies (typep type)
                  (and (valuep val)
                       (equal (type-of-value val)
                              type))))
       :enable (struct-read-member-aux
                member-type-lookup
                member-values-to-types
                member-value-to-type))))

  (defruled defstruct-writer-lemma
    (implies (equal meminfos (member-values-to-types members))
             (b* ((type (member-type-lookup name meminfos))
                  (new-members (struct-write-member-aux name val members)))
               (implies (and (typep type)
                             (valuep val)
                             (equal (type-of-value val)
                                    type))
                        (and (member-value-listp new-members)
                             (equal (member-values-to-types new-members)
                                    meminfos)))))
    :prep-lemmas
    ((defrule lemma
       (b* ((type (member-type-lookup name (member-values-to-types members)))
            (new-members (struct-write-member-aux name val members)))
         (implies (and (typep type)
                       (valuep val)
                       (equal (type-of-value val)
                              type))
                  (and (member-value-listp new-members)
                       (equal (member-values-to-types new-members)
                              (member-values-to-types members)))))
       :enable (struct-write-member-aux
                member-type-lookup
                member-values-to-types
                member-value-to-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-recognizer ((struct-tag-p symbolp)
                                  (tag symbolp)
                                  (members member-type-listp))
  :returns (mv (event pseudo-event-formp)
               (not-error-thm symbolp)
               (valuep-thm symbolp)
               (value-kind-thm symbolp)
               (tag-thm symbolp)
               (members-thm symbolp))
  :short "Generate the recognizer of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This recognizes structures
     with the appropriate types, member names, and member types.")
   (xdoc::p
    "We also generate several theorem;
     see @(tsee defstruct-info)."))
  (b* ((not-errorp-when-struct-tag-p
        (packn-pos (list 'not-errorp-when- struct-tag-p)
                   struct-tag-p))
       (valuep-when-struct-tag-p
        (packn-pos (list 'valuep-when- struct-tag-p)
                   struct-tag-p))
       (value-kind-when-struct-tag-p
        (packn-pos (list 'value-kind-when- struct-tag-p)
                   struct-tag-p))
       (value-struct->tag-when-struct-tag-p
        (packn-pos (list 'value-struct->tag-when- struct-tag-p)
                   struct-tag-p))
       (value-struct->members-when-struct-tag-p
        (packn-pos (list 'value-struct->members-when- struct-tag-p)
                   struct-tag-p))
       (event
        `(define ,struct-tag-p (x)
           :returns (yes/no booleanp)
           (and (valuep x)
                (value-case x :struct)
                (equal (value-struct->tag x)
                       (ident ,(symbol-name tag)))
                (equal (member-values-to-types (value-struct->members x))
                       ',members))
           :hooks (:fix)
           ///
           (defruled ,not-errorp-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (not (errorp x)))
             :enable (errorp ,struct-tag-p valuep))
           (defruled ,valuep-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (valuep x))
             :in-theory '(,struct-tag-p))
           (defruled ,value-kind-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (equal (value-kind x) :struct))
             :in-theory '(,struct-tag-p))
           (defruled ,value-struct->tag-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (equal (value-struct->tag x)
                             (ident ,(symbol-name tag))))
             :in-theory '(,struct-tag-p))
           (defruled ,value-struct->members-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (equal (member-values-to-types (value-struct->members x))
                             ',members))
             :in-theory '(,struct-tag-p)))))
    (mv event
        not-errorp-when-struct-tag-p
        valuep-when-struct-tag-p
        value-kind-when-struct-tag-p
        value-struct->tag-when-struct-tag-p
        value-struct->members-when-struct-tag-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-fixer ((struct-tag-fix symbolp)
                             (struct-tag-p symbolp)
                             (tag symbolp)
                             (members member-type-listp))
  :returns (mv (event pseudo-event-formp)
               (fixer-recognizer-thm symbolp))
  :short "Generate the fixer of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "As the fixing value,
     we pick a structure with the right tag,
     the right member names,
     and zero integer values of the right types for all the members.")
   (xdoc::p
    "We also return the name of the theorem that
     rewrites the fixer away when the recognizer holds."))
  (b* ((event
        `(std::deffixer ,struct-tag-fix
           :pred ,struct-tag-p
           :param x
           :body-fix (if (,struct-tag-p x)
                         x
                       (make-value-struct :tag (ident ,(symbol-name tag))
                                          :members
                                          (list ,@(defstruct-gen-fixer-aux
                                                    members))))))
       (thm (packn-pos (list struct-tag-fix '-when- struct-tag-p)
                       struct-tag-fix)))
    (mv event thm))

  :prepwork
  ((define defstruct-gen-fixer-aux ((members member-type-listp))
     :returns (terms true-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          ((member-type member) (car members))
          (val (case (type-kind member.type)
                 (:uchar '(uchar 0))
                 (:schar '(schar 0))
                 (:ushort '(ushort 0))
                 (:sshort '(sshort 0))
                 (:uint '(uint 0))
                 (:sint '(sint 0))
                 (:ulong '(ulong 0))
                 (:slong '(slong 0))
                 (:ullong '(ullong 0))
                 (:sllong '(sllong 0))
                 (t (raise "Internal error: member type ~x0." member.type))))
          (term `(make-member-value :name ',member.name :value ,val))
          (terms (defstruct-gen-fixer-aux (cdr members))))
       (cons term terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-fixtype ((struct-tag symbolp)
                               (struct-tag-p symbolp)
                               (struct-tag-fix symbolp)
                               (struct-tag-equiv symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the fixtype of
          the structures defined by the @(tsee defstruct)."
  `(fty::deffixtype ,struct-tag
     :pred ,struct-tag-p
     :fix ,struct-tag-fix
     :equiv ,struct-tag-equiv
     :define t
     :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-reader ((struct-tag symbolp)
                              (struct-tag-p symbolp)
                              (struct-tag-fix symbolp)
                              (name identp)
                              (type typep)
                              (members member-type-listp)
                              (wrld plist-worldp))
  :returns (mv (event pseudo-event-formp)
               (reader symbolp)
               (reader-return-thm symbolp))
  :short "Generate the reader for a member of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of @(tsee struct-read-member),
     but it has more specialized input and output types;
     in particular, it never returns an error.
     To prove the output type,
     we need some intermediate lemmas
     about @(tsee struct-read-member) and @('struct-read-member-aux').")
   (xdoc::p
    "Also return the name of the reader
     and the name of the return type theorem of the reader.
     The latter is generated by @(tsee define)."))
  (b* ((typep (atc-type-to-recognizer type wrld))
       (struct-tag-read-name (packn-pos (list struct-tag
                                              '-read-
                                              (ident->name name))
                                        struct-tag))
       (return-thm (packn-pos (list typep '-of- struct-tag-read-name)
                              struct-tag-read-name))
       (event
        `(encapsulate ()
           (defrulel lemma
             (implies (,struct-tag-p struct)
                      (,typep (struct-read-member ',name struct)))
             :enable (,struct-tag-p
                      struct-read-member
                      ,(packn-pos (list typep '-to-type-of-value) typep))
             :use (:instance defstruct-reader-lemma
                   (meminfos ',members)
                   (name ',name)
                   (members (value-struct->members struct))))
           (define ,struct-tag-read-name ((struct ,struct-tag-p))
             :returns (val ,typep)
             (struct-read-member (ident ,(ident->name name))
                                 (,struct-tag-fix struct))
             :guard-hints (("Goal" :in-theory (enable ,struct-tag-p)))
             :hooks (:fix)))))
    (mv event struct-tag-read-name return-thm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-readers ((struct-tag symbolp)
                               (struct-tag-p symbolp)
                               (struct-tag-fix symbolp)
                               (members member-type-listp)
                               (all-members member-type-listp)
                               (wrld plist-worldp))
  :returns (mv (events pseudo-event-form-listp)
               (readers symbol-listp)
               (reader-return-thms symbol-listp))
  :short "Generate the readers for the members of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the list of readers
     and the list of return type theorems of the readers."))
  (b* (((when (endp members)) (mv nil nil nil))
       ((member-type member) (car members))
       ((mv event reader return-thm)
        (defstruct-gen-reader
          struct-tag struct-tag-p struct-tag-fix
          member.name member.type all-members
          wrld))
       ((mv events readers return-thms)
        (defstruct-gen-readers
          struct-tag struct-tag-p struct-tag-fix
          (cdr members) all-members
          wrld)))
    (mv (cons event events)
        (cons reader readers)
        (cons return-thm return-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-writer ((struct-tag symbolp)
                              (struct-tag-p symbolp)
                              (struct-tag-fix symbolp)
                              (name identp)
                              (type typep)
                              (members member-type-listp)
                              (wrld plist-worldp))
  :returns (mv (event pseudo-event-formp)
               (writer symbolp)
               (writer-return-thm symbolp))
  :short "Generate the writer for a member of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of @(tsee struct-write-member),
     but it has more specialized input and output types;
     in particular, it never returns an error.
     To prove the output type,
     we need some intermediate lemmas
     about @(tsee struct-write-member) and @('struct-write-member-aux').")
   (xdoc::p
    "Also return the name of the writer
     and the name of the return type theorem of the writer.
     The latter is generated by @(tsee define)."))
  (b* ((typep (atc-type-to-recognizer type wrld))
       (type-fix (atc-type-to-fixer type wrld))
       (struct-tag-write-name (packn-pos (list struct-tag
                                               '-write-
                                               (ident->name name))
                                         struct-tag))
       (return-thm (packn-pos (list struct-tag-p '-of- struct-tag-write-name)
                              struct-tag-write-name))
       (event
        `(encapsulate ()
           (defrulel lemma
             (implies (and (,struct-tag-p struct)
                           (,typep val))
                      (,struct-tag-p (struct-write-member ',name val struct)))
             :enable (,struct-tag-p
                      struct-write-member
                      ,(packn-pos (list 'type-of-value-when- typep)
                                  'type-of-value))
             :use (:instance defstruct-writer-lemma
                   (meminfos ',members)
                   (name ',name)
                   (members (value-struct->members struct))
                   (val val)))
           (define ,struct-tag-write-name ((val ,typep) (struct ,struct-tag-p))
             :returns (new-struct ,struct-tag-p)
             (struct-write-member (ident ,(ident->name name))
                                  (,type-fix val)
                                  (,struct-tag-fix struct))
             :guard-hints (("Goal" :in-theory (enable ,struct-tag-p)))
             :hooks (:fix)))))
    (mv event struct-tag-write-name return-thm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-writers ((struct-tag symbolp)
                               (struct-tag-p symbolp)
                               (struct-tag-fix symbolp)
                               (members member-type-listp)
                               (all-members member-type-listp)
                               (wrld plist-worldp))
  :returns (mv (events pseudo-event-form-listp)
               (writers symbol-listp)
               (writer-return-thms symbol-listp))
  :short "Generate the writers for the members of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the list of writers
     and the list of return type theorems of the writers."))
  (b* (((when (endp members)) (mv nil nil nil))
       ((member-type member) (car members))
       ((mv event writer return-thm)
        (defstruct-gen-writer
          struct-tag struct-tag-p struct-tag-fix
          member.name member.type all-members
          wrld))
       ((mv events writers return-thms)
        (defstruct-gen-writers
          struct-tag struct-tag-p struct-tag-fix
          (cdr members) all-members
          wrld)))
    (mv (cons event events)
        (cons writer writers)
        (cons return-thm return-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-everything ((tag symbolp)
                                  (tag-ident identp)
                                  (members member-type-listp)
                                  (call pseudo-event-formp)
                                  (wrld plist-worldp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the recognizer, fixer, fixtype, readers, and writers,
     and the table event.")
   (xdoc::p
    "We store the return type theorems of the readers and writers
     into the table."))
  (b* ((struct-tag (packn-pos (list 'struct- tag) tag))
       (struct-tag-p (packn-pos (list struct-tag '-p) tag))
       (struct-tag-fix (packn-pos (list struct-tag '-fix) tag))
       (struct-tag-equiv (packn-pos (list struct-tag '-equiv) tag))
       ((mv recognizer-event
            not-errorp-when-struct-tag-p
            valuep-when-struct-tag-p
            value-kind-when-struct-tag-p
            value-struct->tag-when-struct-tag-p
            value-struct->members-when-struct-tag-p)
        (defstruct-gen-recognizer struct-tag-p tag members))
       ((mv fixer-event
            fixer-recognizer-thm)
        (defstruct-gen-fixer struct-tag-fix struct-tag-p tag members))
       (fixtype-event (defstruct-gen-fixtype
                        struct-tag struct-tag-p
                        struct-tag-fix struct-tag-equiv))
       ((mv reader-events reader-names reader-return-thms)
        (defstruct-gen-readers
          struct-tag struct-tag-p struct-tag-fix members members wrld))
       ((mv writer-events writer-names writer-return-thms)
        (defstruct-gen-writers
          struct-tag struct-tag-p struct-tag-fix members members wrld))
       (info (make-defstruct-info
              :tag tag-ident
              :members members
              :recognizer struct-tag-p
              :fixer struct-tag-fix
              :readers reader-names
              :writers writer-names
              :fixer-recognizer-thm fixer-recognizer-thm
              :reader-return-thms reader-return-thms
              :writer-return-thms writer-return-thms
              :not-error-thm not-errorp-when-struct-tag-p
              :valuep-thm valuep-when-struct-tag-p
              :value-kind-thm value-kind-when-struct-tag-p
              :tag-thm value-struct->tag-when-struct-tag-p
              :members-thm value-struct->members-when-struct-tag-p
              :call call))
       (table-event (defstruct-table-record-event (symbol-name tag) info)))
    `(progn
       ,recognizer-event
       ,fixer-event
       ,fixtype-event
       ,@reader-events
       ,@writer-events
       ,table-event))
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-fn ((args true-listp)
                      (call pseudo-event-formp)
                      (ctx ctxp)
                      state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Process the inputs and generate the events."
  (b* ((wrld (w state))
       ((mv erp (list tag tag-ident members redundant) state)
        (defstruct-process-inputs args call ctx state))
       ((when erp) (mv erp '(_) state))
       ((when redundant) (acl2::value '(value-triple :redundant)))
       (event (defstruct-gen-everything tag tag-ident members call wrld)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defstruct (&whole call &rest args)
  :short "Define a shallowly embedded C structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see shallow-structures)."))
  `(make-event (defstruct-fn ',args ',call 'struct state)))
