(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun s () (_ BitVec 1))
(declare-fun x () (_ BitVec 8))

(assert (= c #b00101011))
(assert (= s #b1))
(assert (= (bvcomp x c) #b1))

(check-sat)

(exit)
