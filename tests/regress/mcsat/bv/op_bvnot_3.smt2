(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 20))
(declare-fun y () (_ BitVec 20))

(assert (= x #b11111111111111111111))
(assert (= y (bvnot x)))

(check-sat)

(exit)

