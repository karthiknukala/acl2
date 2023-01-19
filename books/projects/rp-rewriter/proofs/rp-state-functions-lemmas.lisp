; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "../rp-state-functions")
(include-book "aux-function-lemmas")
(include-book "proof-functions")

(local
 (in-theory (enable rp-statep)))

(local
 (in-theory (disable equal-of-len-with-constant)))

(defthm integerp-of-RW-STACK-SIZE
  (implies (rp-statep rp-state)
           (integerp (RW-STACK-SIZE rp-state)))
  :hints (("Goal"
           :in-theory (e/d (RW-STACK-SIZE
                            rp-statep)
                           ()))))



(defthm RULES-ALIST-OUTSIDE-IN-GET-of-update-nth
  (implies (not (equal index *RULES-ALIST-OUTSIDE-IN-GET*))
           (equal (RULES-ALIST-OUTSIDE-IN-GET key
                                              (update-nth index something
                                                          rp-state))
                  (RULES-ALIST-OUTSIDE-IN-GET key
                                              rp-state)))
  :hints (("Goal"
           :in-theory (e/d (RULES-ALIST-OUTSIDE-IN-GET) ()))))

(defthm RULES-ALIST-inside-out-GET-of-update-nth
  (implies (and (not (equal index *RULES-ALIST-inside-out-GET*))
                (natp index)
                )
           (equal (RULES-ALIST-inside-out-GET key
                                              (update-nth index something
                                                          rp-state))
                  (RULES-ALIST-inside-out-GET key
                                              rp-state)))
  :hints (("Goal"
           :in-theory (e/d (RULES-ALIST-inside-out-GET
                            zp)
                           (rp-statep)))))


(defthm valid-rp-statep-of-update-nth
  (implies (and
            (valid-rp-statep rp-state)
            (natp index)
            (not (equal index *RULES-ALIST-OUTSIDE-IN-GET*))
            (not (equal index *RULES-ALIST-inside-out-GET*)))
           (valid-rp-statep (update-nth index val rp-state)))
  :hints (("Goal"
           :expand ((VALID-RP-STATEP (UPDATE-NTH INDEX VAL RP-STATE)))
           :do-not-induct t
           :use ((:instance valid-rp-statep-necc
                            (key (VALID-RP-STATEP-WITNESS (UPDATE-NTH INDEX VAL RP-STATE)))))
           :in-theory (e/d (RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-inside-out-GET)
                           (valid-rp-statep)))))

(Local
 (in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                     (:DEFINITION RP-TERMP))))

(defthm valid-rp-state-syntaxp-of-update-nth
  (implies (and
            (natp index)
            (valid-rp-state-syntaxp rp-state)
            (rp-statep (update-nth index val rp-state))
            (not (equal index *RULES-ALIST-OUTSIDE-IN-GET*))
            (not (equal index *RULES-ALIST-inside-out-GET*)))
           (valid-rp-state-syntaxp (update-nth index val rp-state)))
  :hints (("Goal"
           :expand ((valid-rp-state-syntaxp (UPDATE-NTH INDEX VAL RP-STATE))
                    (VALID-RP-STATE-SYNTAXP RP-STATE))
           :do-not-induct t
           :do-not '(preprocess fertilize generalize)
           :use ((:instance VALID-RP-STATE-SYNTAXP-aux-necc
                            (key (VALID-RP-STATE-SYNTAXP-AUX-WITNESS (UPDATE-NTH INDEX VAL RP-STATE)))))
           :in-theory (e/d (RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-inside-out-GET)
                           (valid-rp-statep)))))

(defthm VALID-RP-STATE-SYNTAXP-AUX-of-update-nth
  (implies (and
            (natp index)
            (VALID-RP-STATE-SYNTAXP-AUX rp-state)
            (not (equal index *RULES-ALIST-OUTSIDE-IN-GET*))
            (not (equal index *RULES-ALIST-inside-out-GET*)))
           (VALID-RP-STATE-SYNTAXP-AUX (update-nth index val rp-state)))
  :hints (("Goal"
           :expand ((valid-rp-state-syntaxp (UPDATE-NTH INDEX VAL RP-STATE))
                    (VALID-RP-STATE-SYNTAXP RP-STATE))
           :do-not-induct t
           :use ((:instance VALID-RP-STATE-SYNTAXP-aux-necc
                            (key (VALID-RP-STATE-SYNTAXP-AUX-WITNESS (UPDATE-NTH INDEX VAL RP-STATE)))))
           :in-theory (e/d (RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-inside-out-GET)
                           (valid-rp-statep)))))


(defthm rp-state-push-to-try-to-rw-stack-is-rp-statep
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                  rp-context
                                                                  rp-state))))
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-to-try-to-rw-stack)
                           ()))))

(defthm update-casesplitter-cases-is-rp-statep
  (implies (and (rp-statep rp-state)
                (rp-term-listp cases))
           (rp-statep (update-casesplitter-cases cases rp-state)))
  :hints (("goal"
           :in-theory (e/d (update-casesplitter-cases)
                           ()))))

(defthm rules-alist-outside-in-get-and-insideout-get-cancel1
  (and (equal (rules-alist-outside-in-get key (update-rw-stack-size v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (update-rw-stack v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (update-rule-frame-cnts v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (rules-used-put k v rp-state))
              (rules-alist-outside-in-get key rp-state))
       #|(equal (rules-alist-outside-in-get key (update-rules-used v rp-state))
              (rules-alist-outside-in-get key rp-state))||#

       (equal (rules-alist-inside-out-get key (update-rw-stack-size v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (update-rw-stack v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (update-rule-frame-cnts v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (rules-used-put k v rp-state))
              (rules-alist-inside-out-get key rp-state))
       #|(equal (rules-alist-inside-out-get key (update-rules-used v rp-state))
              (rules-alist-inside-out-get key rp-state))||#
       )
  :hints (("goal"
           :in-theory (e/d (rules-alist-outside-in-get
                            rules-alist-inside-out-get)
                           ()))))

#|(local
 (defthm valid-rp-statep-expand
   (implies (syntaxp (not (equal rp-state 'rp-state)))
            (equal (valid-rp-statep rp-state)
                   (let
                    ((key (valid-rp-statep-witness rp-state)))
                    (or
                     (not (symbolp key))
                     (and
                      (valid-rulesp (rules-alist-outside-in-get key rp-state))
                      (valid-rulesp (rules-alist-inside-out-get key
                                                                rp-state)))))))
   :hints (("goal"
            :in-theory (e/d (valid-rp-statep) ())))))||#

(defthm rp-state-push-to-try-to-rw-stack-is-valid-rp-state-syntaxp
  (and (implies (valid-rp-state-syntaxp rp-state)
                (valid-rp-state-syntaxp (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                                    rp-context
                                                                                    rp-state))))
       (implies (valid-rp-statep rp-state)
                (valid-rp-statep (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                             rp-context
                                                                             rp-state)))))
  :hints (("goal"
           :in-theory (e/d (rp-state-push-to-try-to-rw-stack
                            valid-rp-state-syntaxp
                            update-rw-stack)
                           (valid-rp-statep
                            valid-rp-state-syntaxp-aux
                            )))))


(defthm true-list-of-update-nth
  (implies (true-listp lst)
           (true-listp (update-nth n x lst))))

(defthm rp-statep-rp-state-push-to-result-to-rw-stack
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-push-to-result-to-rw-stack rule
                                                           index
                                                           failed
                                                           old-term
                                                           new-term
                                                           rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack)
                           (UNSIGNED-BYTE-P
                            UPDATE-NTH
                            (:TYPE-PRESCRIPTION ALISTP)
                            (:REWRITE DEFAULT-CDR)
                            (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P)
                            (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL)
                            (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:REWRITE NTH-ADD1)
                            EQUAL-OF-LEN-WITH-CONSTANT
                            (:DEFINITION HONS-ASSOC-EQUAL))))))


(defret RULES-ALIST-OUTSIDE-IN-GET-of-RP-STATE-PUSH-TO-RESULT-TO-RW-STACK
  (and (equal (RULES-ALIST-OUTSIDE-IN-GET key res-rp-state)
              (RULES-ALIST-OUTSIDE-IN-GET key rp-state))
       (equal (RULES-ALIST-INSIDE-OUT-GET key res-rp-state)
              (RULES-ALIST-INSIDE-OUT-GET key rp-state)))
  :fn rp-state-push-to-result-to-rw-stack
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack) ()))))

(defthm rp-statep-of-update-rw-stack
  (implies (and (rp-statep rp-state)
                (alistp v))
           (rp-statep (update-rw-stack v rp-state)))
  :hints (("goal"
           :in-theory (e/d () ()))))

(defthm rp-statep-of-UPDATE-RULE-FRAME-CNTS
    (implies (and (rp-statep rp-state)
                  (alistp v))
             (rp-statep (UPDATE-RULE-FRAME-CNTS v rp-state)))
    :hints (("Goal"
             :in-theory (e/d (rp-statep) ()))))

(defthm valid-rp-statep-rp-state-push-to-result-to-rw-stack
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (rp-state-push-to-result-to-rw-stack rule
                                                                 index
                                                                 failed
                                                                 old-term
                                                                 new-term
                                                                 rp-state)))
  :hints (("goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (rp-state-push-to-result-to-rw-stack rule
                                                         index
                                                         failed
                                                         old-term
                                                         new-term
                                                         rp-state)))))
           :in-theory (e/d (;;rp-state-push-to-result-to-rw-stack
                            valid-rp-statep
                            ;;valid-rp-statep-necc
                            )
                           (;;valid-rp-statep
                            update-rule-frame-cnts
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            rp-statep
                            rule-frame-cnts
                            (:rewrite default-cdr)
                            rw-stack
                            nfix
                            hons-acons
                            hons-get
                            fix
                            rw-stack-size
                            rp-brr
                            rp-rune$inline
                            update-rw-stack)))))



(defthm alistp-of-rule-frame-cnts
  (implies (rp-statep rp-state)
           (alistp (rule-frame-cnts rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-statep) ()))))

(defthm alistp-of-rw-stack
  (implies (rp-statep rp-state)
           (alistp (rw-stack rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-statep) ())))) 

(defthm valid-rp-state-syntaxp-rp-state-push-to-result-to-rw-stack
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (rp-state-push-to-result-to-rw-stack rule
                                                                        index
                                                                        failed
                                                                        old-term
                                                                        new-term
                                                                        rp-state)))
  :hints (("goal"
           :use (
                 (:instance rp-statep-rp-state-push-to-result-to-rw-stack)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (rp-state-push-to-result-to-rw-stack rule
                                                         index
                                                         failed
                                                         old-term
                                                         new-term
                                                         rp-state)))))
           :in-theory (e/d (;;rp-state-push-to-result-to-rw-stack
                            valid-rp-state-syntaxp
                            hons-acons)
                           (valid-rp-statep
                            rule-list-syntaxp
                            update-rule-frame-cnts
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            rp-statep
                            rule-frame-cnts
                            (:rewrite default-cdr)
                            rw-stack
                            nfix
                            
                            hons-get
                            fix
                            rw-stack-size
                            rp-brr
                            rp-rune$inline
                            update-rw-stack)))))


(defthm rp-statep-rp-stat-add-to-rules-used
  (implies (rp-statep rp-state)
           (rp-statep (rp-stat-add-to-rules-used rule failed exc-flg rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-stat-add-to-rules-used
                            rp-statep
                            alistp
                            hons-acons) ()))))

(defthm valid-rp-statep-rp-stat-add-to-rules-used
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (rp-stat-add-to-rules-used rule failed exc-flg rp-state)))
  :hints (("goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key (valid-rp-statep-witness
                        (rp-stat-add-to-rules-used rule failed exc-flg rp-state)))))
           :in-theory (e/d (rp-stat-add-to-rules-used

                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            
                            valid-rp-statep)
                           (rp-statep
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                           ;; rules-used-get
                            (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))

(defthm valid-rp-state-syntaxp-rp-stat-add-to-rules-used
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (rp-stat-add-to-rules-used rule failed
                                                              exc-flg rp-state)))
  :hints (("goal"
           :use ((:instance
                  rp-statep-rp-stat-add-to-rules-used)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key (valid-rp-state-syntaxp-aux-witness
                        (rp-stat-add-to-rules-used rule failed exc-flg rp-state)))))
           :in-theory (e/d (rp-stat-add-to-rules-used
                            valid-rp-state-syntaxp

                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            
                            valid-rp-statep)
                           (rp-statep
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                            (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))


(defthm rp-statep-rp-state-new-run
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-state-new-run) ()))))

#|(defthm rp-statep-rp-state-new-run
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-state-new-run) ()))))||#

(defthm rp-statep-rp-state-push-meta-to-rw-stack
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-push-meta-to-rw-stack meta-rule old-term new-term rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-statep
                            rp-state-push-meta-to-rw-stack)
                           ()))))


(defthm rp-statep-of-rules-used-put
  (implies (rp-statep rp-state)
           (rp-statep (rules-used-put k v rp-state)))
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d (rules-used-put
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            rp-state-preservedp)
                           ()))))


(defthm rp-state-preservedp-of-rules-used-put
  (implies (and (rp-state-preservedp rp-state1 rp-state2))
           (rp-state-preservedp rp-state1
                                (rules-used-put k v rp-state2)))
  :hints (("goal"
           :do-not-induct t
           :expand (rp-state-preservedp-sk rp-state1
                                           (update-nth 5 (cons (cons k v) (nth 5 rp-state2))
                                                       rp-state2))
           :use ((:instance rp-statep-of-rules-used-put
                            (rp-state rp-state2))
                 (:instance rp-state-preservedp-sk-necc
                            (key (rp-state-preservedp-sk-witness
                                  rp-state1
                                  (update-nth 5 (cons (cons k v) (nth 5 rp-state2))
                                              rp-state2)))
                            (old-rp-state rp-state1)
                            (new-rp-state rp-state2)))
           :in-theory (e/d (rules-used-put
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            rp-state-preservedp)
                           (;;rp-statep
                            rp-statep-of-rules-used-put
                            rp-state-preservedp-sk)))))




(defthm rp-state-preservedp-rp-stat-add-to-rules-used
  (implies (rp-state-preservedp rp-state1 rp-state2)
           (rp-state-preservedp rp-state1
                                (rp-stat-add-to-rules-used rule failed flg
                                                           rp-state2)))
  :hints (("goal"
           :do-not-induct t 
           :in-theory (e/d (rp-stat-add-to-rules-used
                            ;; rules-alist-outside-in-get
                            ;; rules-alist-inside-out-get
                            ;;rp-state-preservedp
                            valid-rp-statep)
                           (rp-statep
                            rules-used-put
                            rules-used-get
                            rules-used-boundp
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                           ;; rules-used-get
                            (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))


(defthm rp-statep-of-update-rw-stack-size
  (implies (and (rp-statep rp-state)
                (integerp v)
                )
           (rp-statep (update-rw-stack-size v rp-state)))
  :hints (("goal"
           :in-theory (e/d () ()))))
  

(defthm rp-state-preservedp-of-update-rw-stack-size
  (implies (and (rp-state-preservedp rp-state1 rp-state2)
                (force (integerp v)))
           (rp-state-preservedp rp-state1
                                (update-rw-stack-size v rp-state2)))
  :hints (("goal"
           :do-not-induct t
           :expand (rp-state-preservedp-sk rp-state1 (update-nth 7 v rp-state2))
           :use ((:instance rp-statep-of-update-rw-stack-size
                            (rp-state rp-state2))
                 (:instance rp-state-preservedp-sk-necc
                            (key (rp-state-preservedp-sk-witness rp-state1 (update-nth 7 v rp-state2)))
                            (old-rp-state rp-state1)
                            (new-rp-state rp-state2)))
           :in-theory (e/d (rules-used-put
                            update-rw-stack-size
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            rp-state-preservedp)
                           (;;rp-statep
                            rp-statep-of-rules-used-put
                            rp-state-preservedp-sk)))))

(defthm valid-rp-statep-of-update-rw-stack-size
  (implies (and (valid-rp-statep rp-state))
           (valid-rp-statep (update-rw-stack-size v rp-state)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (update-rw-stack-size v rp-state)))))
           :in-theory (e/d (update-rw-stack-size
                            ;;RULES-ALIST-OUTSIDE-IN-GET
                            ;;RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep)
                           (rp-statep)))))

(defthm VALID-RP-STATE-SYNTAXP-of-update-rw-stack-size
  (implies (and (VALID-RP-STATE-SYNTAXP rp-state)
                (integerp v))
           (VALID-RP-STATE-SYNTAXP (update-rw-stack-size v rp-state)))
  :hints (("Goal"
           :do-not-induct t
           
           :in-theory (e/d (RP-STATEP
                            update-rw-stack-size
                            ;;RULES-ALIST-OUTSIDE-IN-GET
                            ;;RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep
                            VALID-RP-STATE-SYNTAXP)
                           ()))))



(defthm rp-state-preservedp-of-update-rw-stack
  (implies (and (rp-state-preservedp rp-state1 rp-state2)
                (force (alistp v)))
           (rp-state-preservedp rp-state1
                                (update-rw-stack v rp-state2)))
  :hints (("goal"
           :do-not-induct t
           :expand (rp-state-preservedp-sk rp-state1 (update-nth 8 v rp-state2))
           :use ((:instance rp-statep-of-update-rw-stack
                            (rp-state rp-state2))
                 (:instance rp-state-preservedp-sk-necc
                            (key (rp-state-preservedp-sk-witness rp-state1 (update-nth 8 v rp-state2)))
                            (old-rp-state rp-state1)
                            (new-rp-state rp-state2)))
           :in-theory (e/d (rules-used-put
                            update-rw-stack-size
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            rp-state-preservedp)
                           (;;rp-statep
                            rp-statep-of-rules-used-put
                            rp-state-preservedp-sk)))))


(defthm valid-rp-statep-of-update-rw-stack
  (implies (and (valid-rp-statep rp-state))
           (valid-rp-statep (update-rw-stack v rp-state)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (update-rw-stack v rp-state)))))
           :in-theory (e/d (update-rw-stack
                            ;;RULES-ALIST-OUTSIDE-IN-GET
                            ;;RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep)
                           (rp-statep)))))

(defthm VALID-RP-STATE-SYNTAXP-of-update-rw-stack
  (implies (and (VALID-RP-STATE-SYNTAXP rp-state)
                 (ALISTP V))
           (VALID-RP-STATE-SYNTAXP (update-rw-stack v rp-state)))
  :hints (("Goal"
           :do-not-induct t
           
           :in-theory (e/d (VALID-RP-STATE-SYNTAXP
                            update-rw-stack
                            RP-STATEP
                            ;;RULES-ALIST-OUTSIDE-IN-GET
                            ;;RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep)
                           ()))))

(defthm rp-state-preservedp-implies-alistp
  (implies (rp-state-preservedp rpstate1 rp-state2)
           (rp-statep rp-state2))
  :hints (("goal"
           :in-theory (e/d (rp-state-preservedp) ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm rp-state-preservedp-rp-state-push-meta-to-rw-stack
  (implies (rp-state-preservedp rp-state1 rp-state2)
           (rp-state-preservedp rp-state1
                                (rp-state-push-meta-to-rw-stack meta-rule old-term new-term
                                                                rp-state2)))
  :hints (("goal"
           :do-not-induct t 
           :in-theory (e/d (rp-state-push-meta-to-rw-stack
                            ;; rules-alist-outside-in-get
                            ;; rules-alist-inside-out-get
                            ;;rp-state-preservedp
                            valid-rp-statep
                            alistp)
                           (rp-statep
                            update-rw-stack-size
                            update-rw-stack
                            rw-stack-size
                            rw-stack
                            rules-used-put
                            rules-used-get
                            rules-used-boundp
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                           ;; rules-used-get
                           ;; (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))

(defthm valid-rp-statep-push-meta-to-rw-stack
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (rp-state-push-meta-to-rw-stack meta-rule old-term new-term rp-state)))
  :hints (("goal"
           :do-not-induct t 
           :in-theory (e/d (rp-state-push-meta-to-rw-stack
                            ;; rules-alist-outside-in-get
                            ;; rules-alist-inside-out-get
                            ;;rp-state-preservedp
                            
                            alistp)
                           (valid-rp-statep
                            rp-statep
                            update-rw-stack-size
                            update-rw-stack
                            rw-stack-size
                            rw-stack
                            rules-used-put
                            rules-used-get
                            rules-used-boundp
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                           ;; rules-used-get
                           ;; (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))


(local
 (defthm dummy-integerp-lemma
   (implies (integerp x)
            (integerp (1+ x)))))

(defthm valid-rp-state-syntaxp-meta-to-rw-stack
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (rp-state-push-meta-to-rw-stack meta-rule old-term new-term rp-state)))
  :hints (("goal"
           
           :do-not-induct t 
           :in-theory (e/d (rp-state-push-meta-to-rw-stack
                            
                            ;; rules-alist-outside-in-get
                            ;; rules-alist-inside-out-get
                            ;;rp-state-preservedp
                            
                            alistp)
                           (VALID-RP-STATE-SYNTAXP
                            VALID-RP-STATE-SYNTAXP-aux
                            valid-rp-statep
                            rp-statep
                            update-rw-stack-size
                            update-rw-stack
                            rw-stack-size
                            rw-stack
                            rules-used-put
                            rules-used-get
                            rules-used-boundp
                            ;;update-rules-used
                            (:definition valid-sc-nt)
;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                           ;; rules-used-get
                           ;; (:definition not)
                            ;;(:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))

(defthm valid-rp-state-syntaxp-update-casesplitter-cases-is-rp-statep
  (implies (and (valid-rp-state-syntaxp rp-state)
                (rp-term-listp cases)
                )
           (valid-rp-state-syntaxp (update-casesplitter-cases cases rp-state)))
  :hints (("goal"
           :use ((:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (update-casesplitter-cases cases rp-state)))))
           :in-theory (e/d (update-casesplitter-cases
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            valid-rp-state-syntaxp)
                           ()))))

(defthm rp-state-preservedp-of-update-casesplitter-cases
  (implies (and (rp-state-preservedp rp-state1 rp-state2)
                (force (rp-term-listp cases)))
           (rp-state-preservedp rp-state1
                                (update-casesplitter-cases cases rp-state2)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x)
                           (RP-STATE-PRESERVEDP-SK RP-STATE1 (UPDATE-NTH x CASES RP-STATE2))))
           :use ((:instance RP-STATEP-of-UPDATE-RW-STACK
                            (rp-state rp-state2))
                 (:instance RP-STATE-PRESERVEDP-SK-necc
                            (key (RP-STATE-PRESERVEDP-SK-WITNESS RP-STATE1 (update-casesplitter-cases cases rp-state2)))
                            (old-rp-state rp-state1)
                            (new-rp-state rp-state2)))
           :in-theory (e/d (RULES-USED-PUT
                            update-casesplitter-cases
                            RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-INSIDE-OUT-GET
                            RP-STATE-PRESERVEDP)
                           (;;rp-statep
                            RP-STATEP-of-RULES-USED-PUT
                            rp-state-preservedp-sk)))))


(progn
  (defret rp-statep-of-limit-reached-action
    (implies (rp-statep rp-state)
             (rp-statep res-rp-state))
    :fn limit-reached-action
    :hints (("Goal"
             :in-theory (e/d (limit-reached-action) ()))))

  (defret valid-rp-state-syntaxp-of-limit-reached-action
    (implies (valid-rp-state-syntaxp rp-state)
             (valid-rp-state-syntaxp res-rp-state))
    :fn limit-reached-action
    :hints (("Goal"
             :in-theory (e/d (limit-reached-action) ()))))

  (defret valid-rp-statep-of-limit-reached-action
    (implies (valid-rp-statep rp-state)
             (valid-rp-statep res-rp-state))
    :fn limit-reached-action
    :hints (("Goal"
             :in-theory (e/d (limit-reached-action) ())))))






;;;;;;;;


(defthm RULE-LIST-SYNTAXP-of-RULES-ALIST-OUTSIDE-IN-GET/inside-out-get
  (implies (and (valid-rp-state-syntaxp rp-state)
                (symbolp key))
           (and (rule-list-syntaxp (RULES-ALIST-OUTSIDE-IN-GET key rp-state))
                (rule-list-syntaxp (RULES-ALIST-inside-out-GET key rp-state))
                ))
  :hints (("Goal"
           :use ((:instance VALID-RP-STATE-SYNTAXP-AUX-necc
                            ))
           :in-theory (e/d (valid-rp-state-syntaxp)
                           ()))))




(defret rp-statep-of-post-backchain-ops
  (implies (and (rp-statep rp-state))
           (rp-statep res-rp-state))
  :fn post-backchain-ops
  :hints (("Goal"
           :in-theory (e/d (post-backchain-ops
                            rp-statep)
                           ()))))

(defret valid-rp-statep-of-post-backchain-ops
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep res-rp-state))
  :fn post-backchain-ops
  :hints (("Goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (POST-BACKCHAIN-OPS BACKCHAIN-ENDS
                                        RP-STATE)))))
           :in-theory (e/d (post-backchain-ops
                            RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep)
                           (rp-statep)))))

(defret valid-rp-state-syntaxp-of-post-backchain-ops
  (implies (and (valid-rp-state-syntaxp rp-state))
           (valid-rp-state-syntaxp res-rp-state))
  :fn post-backchain-ops
  :hints (("Goal"
           :use ((:instance rp-statep-of-post-backchain-ops)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (post-backchain-ops BACKCHAIN-ENDS ;
                                        RP-STATE)))))
           :in-theory (e/d (post-backchain-ops
                            valid-rp-state-syntaxp                        
                            rp-statep)
                           (valid-rp-statep
                            rp-statep)))))

(defret rp-state-preservedp-of-post-backchain-ops
  (implies (rp-state-preservedp rp-state-old rp-state)
           (rp-state-preservedp rp-state-old res-rp-state))
  :fn post-backchain-ops
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                             (UPDATE-NTH *BACKCHAINING-RULE* NIL RP-STATE)))
           :use ((:instance rp-statep-of-post-backchain-ops)
                 (:instance
                  RP-STATE-PRESERVEDP-SK-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS RP-STATE-OLD
                                                   (UPDATE-NTH *BACKCHAINING-RULE* NIL RP-STATE)))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state))
                 #|(:instance
                  RP-STATE-PRESERVEDP-SK-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS
                    RP-STATE-OLD
                    (UPDATE-NTH *RW-LIMIT-THROWS-ERROR*
                                OLD-LIMIT-ERROR-SETTING
                                (UPDATE-NTH *BACKCHAINING-RULE* NIL
                                            (UPDATE-NTH *BACKCHAINING-JUST-STARTED*
                                                        NIL RP-STATE)))))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state))|#)
           :in-theory (e/d (post-backchain-ops
                            RP-STATE-PRESERVEDP                        
                            UPDATE-RW-LIMIT-THROWS-ERROR
                            )
                           (;;UPDATE-BACKCHAINING-JUST-STARTED
                            ;;UPDATE-BACKCHAINING-RULE
                            valid-rp-statep
                            RP-STATE-PRESERVEDP-sk
                            rp-statep)))))




(defret rp-statep-of-try-to-update-backchaining-rule
  (implies (and (rp-statep rp-state))
           (rp-statep res-rp-state))
  :fn try-to-update-backchaining-rule
  :hints (("Goal"
           :in-theory (e/d (try-to-update-backchaining-rule
                            rp-statep)
                           ()))))

(defret valid-rp-statep-of-try-to-update-backchaining-rule
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep res-rp-state))
  :fn try-to-update-backchaining-rule
  :hints (("goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (mv-nth 1 (try-to-update-backchaining-rule rule
                                                               rp-state))))))
           :in-theory (e/d (try-to-update-backchaining-rule
                            rules-alist-outside-in-get
                            rules-alist-inside-out-get
                            valid-rp-statep)
                           (rp-statep)))))

(defret valid-rp-state-syntaxp-of-try-to-update-backchaining-rule
  (implies (and (valid-rp-state-syntaxp rp-state))
           (valid-rp-state-syntaxp res-rp-state))
  :fn try-to-update-backchaining-rule
  :hints (("Goal"
           :use ((:instance rp-statep-of-try-to-update-backchaining-rule)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (try-to-update-backchaining-rule rule
                                        RP-STATE)))))
           :in-theory (e/d (try-to-update-backchaining-rule
                            valid-rp-state-syntaxp                        
                            rp-statep)
                           (valid-rp-statep
                            rp-statep)))))


(defret rp-statep-of-INCREMENT-RW-STACK-SIZE
  (implies (and (rp-statep rp-state))
           (rp-statep res-rp-state))
  :fn INCREMENT-RW-STACK-SIZE
  :hints (("Goal"
           :in-theory (e/d (INCREMENT-RW-STACK-SIZE
                            rp-statep)
                           ()))))

(defret valid-rp-statep-of-INCREMENT-RW-STACK-SIZE
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep res-rp-state))
  :fn INCREMENT-RW-STACK-SIZE
  :hints (("Goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (INCREMENT-RW-STACK-SIZE RP-STATE)))))
           :in-theory (e/d (INCREMENT-RW-STACK-SIZE
                            RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-INSIDE-OUT-GET
                            valid-rp-statep)
                           (rp-statep)))))

(defret valid-rp-state-syntaxp-of-INCREMENT-RW-STACK-SIZE
  (implies (and (valid-rp-state-syntaxp rp-state)
                (booleanp old-limit-error-setting))
           (valid-rp-state-syntaxp res-rp-state))
  :fn INCREMENT-RW-STACK-SIZE
  :hints (("Goal"
           :use ((:instance rp-statep-of-INCREMENT-RW-STACK-SIZE)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (INCREMENT-RW-STACK-SIZE RP-STATE)))))
           :in-theory (e/d (INCREMENT-RW-STACK-SIZE
                            valid-rp-state-syntaxp                        
                            rp-statep)
                           (valid-rp-statep
                            rp-statep)))))




(defret RP-STATE-PRESERVEDP-of-INCREMENT-RW-STACK-SIZE
  (implies (rp-state-preservedp rp-state-old rp-state)
           (rp-state-preservedp rp-state-old  res-rp-state))
  :fn INCREMENT-RW-STACK-SIZE
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                                            (UPDATE-NTH *RW-STACK-SIZE*
                                                        (+ 1 (NTH *RW-STACK-SIZE* RP-STATE))
                                                        RP-STATE)))
           :use ((:instance rp-statep-of-INCREMENT-RW-STACK-SIZE)
                 (:instance
                  rp-state-preservedp-sk-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS
                    RP-STATE-OLD
                    (UPDATE-NTH *RW-STACK-SIZE*
                                (+ 1 (NTH *RW-STACK-SIZE* RP-STATE))
                                RP-STATE)))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state)))
           :in-theory (e/d (INCREMENT-RW-STACK-SIZE
                            RP-STATE-PRESERVEDP                        
                            )
                           (valid-rp-statep
                            RP-STATE-PRESERVEDP-SK
                            rp-statep)))))



(progn
  (defthm rp-statep-of-update-rw-context-disabled
    (implies (and (rp-statep rp-state)
                  (booleanp flg))
             (rp-statep (UPDATE-RW-CONTEXT-DISABLED flg rp-state)))
    :hints (("Goal"
             :in-theory (e/d () ()))))

  (defthm valid-rp-state-syntaxp-update-rw-context-disabled
    (implies (and (valid-rp-state-syntaxp rp-state)
                  (booleanp flg))
             (valid-rp-state-syntaxp (UPDATE-RW-CONTEXT-DISABLED flg
                                                                   rp-state)))
    :hints (("Goal"
             :in-theory (e/d (VALID-RP-STATE-SYNTAXP) ()))))

  (defthm valid-rp-statep-update-rw-context-disabled
    (implies (and (valid-rp-statep rp-state)
                  (booleanp flg))
             (valid-rp-statep (UPDATE-RW-CONTEXT-DISABLED flg rp-state)))
    :hints (("Goal"
             :in-theory (e/d () ()))))


  (defthm RP-STATE-PRESERVEDP-of-UPDATE-RW-CONTEXT-DISABLED
    (implies (and (rp-state-preservedp rp-state-old rp-state)
                  (booleanp flg))
           (rp-state-preservedp rp-state-old (UPDATE-RW-CONTEXT-DISABLED flg rp-state)))
  
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                            (UPDATE-NTH *RW-CONTEXT-DISABLED* FLG RP-STATE)))
           :use ((:instance rp-statep-of-update-rw-context-disabled)
                 (:instance
                  rp-state-preservedp-sk-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS
                      RP-STATE-OLD
                      (UPDATE-NTH *RW-CONTEXT-DISABLED* FLG RP-STATE)))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state)))
           :in-theory (e/d (
                            RP-STATE-PRESERVEDP                        
                            UPDATE-RW-CONTEXT-DISABLED)
                           (valid-rp-statep
                            RP-STATE-PRESERVEDP-SK
                            rp-statep)))))


  (in-theory (disable update-rw-context-disabled)))



(progn
 (defthm UPDATE-RW-LIMIT-THROWS-ERROR-rp-statep
   (implies (and (rp-statep rp-state)
                 (booleanp flg))
            (rp-statep (update-rw-limit-throws-error flg rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp-statep
                             UPDATE-RW-LIMIT-THROWS-ERROR) ()))))

 (defthm RP-STATE-PRESERVEDP-of-update-rw-limit-throws-error
    (implies (and (rp-state-preservedp rp-state-old rp-state)
                  (booleanp flg))
           (rp-state-preservedp rp-state-old (update-rw-limit-throws-error flg rp-state)))
  
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                          (UPDATE-NTH *RW-LIMIT-THROWS-ERROR* FLG RP-STATE)))
           :use ((:instance UPDATE-RW-LIMIT-THROWS-ERROR-rp-statep)
                 (:instance
                  rp-state-preservedp-sk-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS
                    RP-STATE-OLD
                    (UPDATE-NTH *RW-LIMIT-THROWS-ERROR* FLG RP-STATE)))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state)))
           :in-theory (e/d (
                            RP-STATE-PRESERVEDP                        
                            update-rw-limit-throws-error)
                           (valid-rp-statep
                            RP-STATE-PRESERVEDP-SK
                            rp-statep)))))

 )


(progn
 (defthm UPDATE-RW-LIMIT-THROWS-ERROR-rp-statep
   (implies (and (rp-statep rp-state)
                 (booleanp flg))
            (rp-statep (update-rw-limit-throws-error flg rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp-statep
                             UPDATE-RW-LIMIT-THROWS-ERROR) ()))))

 (defthm RP-STATE-PRESERVEDP-of-update-rw-limit-throws-error
    (implies (and (rp-state-preservedp rp-state-old rp-state)
                  (booleanp flg))
           (rp-state-preservedp rp-state-old (update-rw-limit-throws-error flg rp-state)))
  
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                          (UPDATE-NTH *RW-LIMIT-THROWS-ERROR* FLG RP-STATE)))
           :use ((:instance UPDATE-RW-LIMIT-THROWS-ERROR-rp-statep)
                 (:instance
                  rp-state-preservedp-sk-necc
                  (key
                   (RP-STATE-PRESERVEDP-SK-WITNESS
                    RP-STATE-OLD
                    (UPDATE-NTH *RW-LIMIT-THROWS-ERROR* FLG RP-STATE)))
                  (old-rp-state rp-state-old)
                  (new-rp-state rp-state)))
           :in-theory (e/d (
                            RP-STATE-PRESERVEDP                        
                            update-rw-limit-throws-error)
                           (valid-rp-statep
                            RP-STATE-PRESERVEDP-SK
                            rp-statep)))))

 )


(progn
  

  (defthm valid-rp-state-syntaxp-UPDATE-RULE-FRAME-CNTS
    (implies (and (valid-rp-state-syntaxp rp-state)
                  (alistp v))
             (valid-rp-state-syntaxp (UPDATE-RULE-FRAME-CNTS v
                                                                   rp-state)))
    :hints (("Goal"
             :use ((:instance rp-statep-of-UPDATE-RULE-FRAME-CNTS))
             :in-theory (e/d (VALID-RP-STATE-SYNTAXP) ()))))

  (defthm valid-rp-statep-UPDATE-RULE-FRAME-CNTS
    (implies (and (valid-rp-statep rp-state)
                  (alistp v))
             (valid-rp-statep (UPDATE-RULE-FRAME-CNTS v rp-state)))
    :hints (("Goal"
             :in-theory (e/d () ()))))


  (defthm RP-STATE-PRESERVEDP-of-UPDATE-RULE-FRAME-CNTS
    (implies (and (rp-state-preservedp rp-state-old rp-state)
                  (alistp v))
             (rp-state-preservedp rp-state-old (UPDATE-RULE-FRAME-CNTS v rp-state)))
  
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-STATE-PRESERVEDP-SK RP-STATE-OLD
                                              (UPDATE-NTH *RULE-FRAME-CNTS* v RP-STATE)))
             :use ((:instance rp-statep-of-UPDATE-RULE-FRAME-CNTS)
                   (:instance
                    rp-state-preservedp-sk-necc
                    (key
                     (RP-STATE-PRESERVEDP-SK-WITNESS
                      RP-STATE-OLD
                      (UPDATE-NTH *RULE-FRAME-CNTS* v RP-STATE)))
                    (old-rp-state rp-state-old)
                    (new-rp-state rp-state)))
             :in-theory (e/d (
                              RP-STATE-PRESERVEDP                        
                              UPDATE-RULE-FRAME-CNTS)
                             (valid-rp-statep
                              RP-STATE-PRESERVEDP-SK
                              rp-statep)))))


  (in-theory (disable UPDATE-RULE-FRAME-CNTS)))






(defthm RP-STATE-PRESERVEDP-of-rp-state-push-to-result-to-rw-stack
  (implies (and (rp-state-preservedp rp-state-old rp-state))
           (rp-state-preservedp rp-state-old (rp-state-push-to-result-to-rw-stack rule
                                                                                  index
                                                                                  failed
                                                                                  old-term
                                                                                  new-term
                                                                                  rp-state)))
  
  :hints (("Goal"
           :expand ((RP-STATE-PRESERVEDP RP-STATE-OLD RP-STATE))
           :use ((:instance rp-statep-rp-state-push-to-result-to-rw-stack)
                 #|(:instance
                 rp-state-preservedp-sk-necc ;
                 (key ;
                 (RP-STATE-PRESERVEDP-SK-WITNESS ;
                 RP-STATE-OLD ;
                 (UPDATE-NTH *RW-STACK* ;
                 (CONS (LIST INDEX (LIST :TYPE FAILED) ;
                 (LIST :RUNE (CDDDR RULE)) ;
                 (LIST :NEW-TERM NEW-TERM) ;
                 (LIST :OLD-TERM OLD-TERM)) ;
                 (NTH *RW-STACK* RP-STATE)) ;
                 (UPDATE-NTH *RULE-FRAME-CNTS* ;
                 (CONS (CONS (CDDDR RULE) ;
                 (+ -1 (- INDEX) ;
                 (NTH *RW-STACK-SIZE* RP-STATE))) ;
                 (NTH *RULE-FRAME-CNTS* RP-STATE)) ;
                 RP-STATE)))) ;
                 (old-rp-state rp-state-old) ;
                 (new-rp-state rp-state))|#)
           :in-theory (e/d (alistp
                            
                            ;;RP-STATE-PRESERVEDP                        
                            rp-state-push-to-result-to-rw-stack)
                           (RW-STACK-SIZE
                            RW-STACK
                            RULE-FRAME-CNTS
                            valid-rp-statep
                            UPDATE-RULE-FRAME-CNTS
                            UPDATE-RW-STACK
                            RP-STATE-PRESERVEDP-SK
                            rp-statep)))))

(defret RP-STATE-PRESERVEDP-of-limit-reached-action
    (implies (rp-state-preservedp rp-state-old rp-state)
             (rp-state-preservedp rp-state-old res-rp-state))
    :fn limit-reached-action
    :hints (("Goal"
             :in-theory (e/d (limit-reached-action
                              INCREMENT-RW-STACK-SIZE
                              ;;RP-STATE-PRESERVEDP                        
                              )
                             (valid-rp-statep
                              RP-STATE-PRESERVEDP-SK
                              rp-statep)))))
