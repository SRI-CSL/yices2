(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 5))

(assert (= #b1 ((_ extract 3 3) x)))

(check-sat)

(exit)

