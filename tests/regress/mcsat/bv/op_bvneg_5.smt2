(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 86))
(declare-fun y () (_ BitVec 86))
(declare-fun z () (_ BitVec 86))

(declare-fun o1 () (_ BitVec 86))
(declare-fun o2 () (_ BitVec 86))
(declare-fun o3 () (_ BitVec 86))

(assert (= x #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(assert (= y #b11111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
(assert (= z #b01010010100101001010101010010100101001010101010101010101010101010101010101010101010101))

(assert (= o1 (bvneg x)))
(assert (= o2 (bvneg y)))
(assert (= o3 (bvneg z)))

(check-sat)

(exit)

