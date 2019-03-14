(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 7))
(declare-fun y () (_ BitVec 9))
(declare-fun z () (_ BitVec 16))

(assert (= x #b0101010))
(assert (= y #b101010101))

(assert (= z (concat x y)))

(check-sat)

(exit)

