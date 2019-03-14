(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b10101011))
(assert (= s #b11110101))
(assert (= (bvashr c x) s))

(check-sat)

(exit)
