(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 1))
(declare-fun b () Bool)

(assert (= x (ite b #b0 #b1)))

(check-sat)

(exit)

