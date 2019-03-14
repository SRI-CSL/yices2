(set-logic QF_BV)
(set-info :status sat)

(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= s #b11101001))
(assert (= (bvneg x) s))

(check-sat)

(exit)
