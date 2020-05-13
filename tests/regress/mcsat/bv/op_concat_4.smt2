(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 64))

(assert (= x #b00000000000000000000000000000000))
(assert (= y #b11111111111111111111111111111111))

(assert (= z (concat x y)))

(check-sat)

(exit)

