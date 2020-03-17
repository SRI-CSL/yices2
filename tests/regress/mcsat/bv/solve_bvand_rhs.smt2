(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b01110111))
(assert (= s #b01010101))
(assert (= (bvand c x) s))

(check-sat)

(exit)
