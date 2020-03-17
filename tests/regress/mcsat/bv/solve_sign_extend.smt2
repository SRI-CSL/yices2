(set-logic QF_BV)
(set-info :status sat)

(declare-fun s () (_ BitVec 16))
(declare-fun x () (_ BitVec 8))

(assert (= s #b1111111110111001))
(assert (= ((_ sign_extend 8) x) s))

(check-sat)

(exit)
