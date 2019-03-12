(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 10))

(assert (= x #b00000))
(assert (= y #b11111))

(assert (= z (concat x y)))

(check-sat)

(exit)

