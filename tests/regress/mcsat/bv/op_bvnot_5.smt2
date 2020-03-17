(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 80))
(declare-fun y () (_ BitVec 80))

(assert (= x #b11111111111111111111000000000000000000001111111111111111111100000000000000000000))
(assert (= y (bvnot x)))

(check-sat)

(exit)

