(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun NODE0 () (_ BitVec 32))
(declare-fun NODE1 () (_ BitVec 32))
(assert
  (not
    (let ((NODE2 (bvadd NODE0 NODE1)))
      (let ((NODE3 (bvadd NODE1 NODE0)))
        (= NODE2 NODE3)))))
(check-sat)
