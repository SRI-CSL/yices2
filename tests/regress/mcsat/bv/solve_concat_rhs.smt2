(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 16))
(declare-fun x () (_ BitVec 8))

(assert (= c #b10000111))
(assert (= s #b1000011100011011))
(assert (= (concat c x) s))

(check-sat)

(exit)
