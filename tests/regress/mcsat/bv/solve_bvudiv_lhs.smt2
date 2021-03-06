(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b00000111))
(assert (= s #b00011011))
(assert (= (bvudiv x c) s))

(check-sat)

(exit)
