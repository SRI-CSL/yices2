(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b11101100))
(assert (= s #b11111111))
(assert (= (bvsdiv c x) s))

(check-sat)

(exit)
