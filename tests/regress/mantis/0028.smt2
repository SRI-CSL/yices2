(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(assert (= x (bvlshr (_ bv0 64) (bvmul (_ bv0 64) (_ bv8 64)))))
(check-sat)
