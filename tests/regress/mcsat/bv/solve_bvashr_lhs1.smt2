(set-logic QF_BV)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= (bvashr x c) s))
(assert (= c #b00001111))
(assert (= s #b11111111))

(check-sat)

(exit)
