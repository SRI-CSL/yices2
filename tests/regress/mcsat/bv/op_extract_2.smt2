(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 1))

(assert (= x #b01010))
(assert (= y ((_ extract 4 4) x)))

(check-sat)

(exit)

