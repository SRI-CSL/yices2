(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 32))

(assert (= x #b0000000000000000))
(assert (= y #b1111111111111111))

(assert (= z (concat x y)))

(check-sat)

(exit)

