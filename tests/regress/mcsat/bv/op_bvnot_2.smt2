(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 10))
(declare-fun y () (_ BitVec 10))

(assert (= x #b0000000000))
(assert (= y (bvnot x)))

(check-sat)

(exit)

