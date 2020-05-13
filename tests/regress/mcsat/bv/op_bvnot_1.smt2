(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 5))

(assert (= x #b00000))
(assert (= y (bvnot x)))

(check-sat)

(exit)

