(set-logic QF_BV)

(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(declare-fun z () (_ BitVec 1))

(assert (= (bvand z ((_ extract 1 1) (bvmul x y))) (_ bv1 1)))

(check-sat)
(exit)
