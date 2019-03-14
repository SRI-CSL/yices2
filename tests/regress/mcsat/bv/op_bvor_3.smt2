(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 21))
(declare-fun y () (_ BitVec 21))
(declare-fun z () (_ BitVec 21))

(declare-fun o1 () (_ BitVec 21))
(declare-fun o2 () (_ BitVec 21))
(declare-fun o3 () (_ BitVec 21))

(assert (= x #b000000000000000000000))
(assert (= y #b111111111111111111111))
(assert (= z #b010100101001010010101))

(assert (= o1 (bvor x y)))
(assert (= o2 (bvor y z)))
(assert (= o3 (bvor z x)))

(check-sat)

(exit)

