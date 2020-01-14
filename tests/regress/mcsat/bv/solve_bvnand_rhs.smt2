(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b01010111))
(assert (= s #b11101001))
(assert (= (bvnand c x) s))

(check-sat)

(exit)
