(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 96))

(assert (= x #b0000000000000000000000000000000000000000000000000000000000000000))
(assert (= y #b11111111111111111111111111111111))

(assert (= z (concat x y)))

(check-sat)

(exit)

