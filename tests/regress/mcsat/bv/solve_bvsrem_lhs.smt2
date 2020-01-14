(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= c #b10000111))
(assert (= s #b10011011))
(assert (= (bvsrem x c) s))

(check-sat)

(exit)
