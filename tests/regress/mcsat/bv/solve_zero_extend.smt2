(set-logic QF_BV)
(set-info :status sat)

(declare-fun s () (_ BitVec 16))
(declare-fun x () (_ BitVec 8))

(assert (= s #b0000000011100110))
(assert (= ((_ zero_extend 8) x) s))

(check-sat)

(exit)
