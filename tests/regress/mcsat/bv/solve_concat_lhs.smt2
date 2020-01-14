(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 16))
(declare-fun x () (_ BitVec 8))

(assert (= c #b10000111))
(assert (= s #b0001101110000111))
(assert (= (concat x c) s))

(check-sat)

(exit)
