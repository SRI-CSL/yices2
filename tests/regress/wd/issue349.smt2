(set-logic BV)
(set-info :smt-lib-version 2.0)

(declare-fun const1 () (_ BitVec 32))
(assert (= const1 (_ bv214013 32)))
(declare-fun const2 () (_ BitVec 32))
(assert (= const2 (_ bv2531011 32)))

(declare-fun rand ((_ BitVec 32)) (_ BitVec 32))
(assert (forall ((x (_ BitVec 32)))
        (= (rand x) (bvadd (bvmul x const1) const2))))

(declare-fun state1 () (_ BitVec 32))
(declare-fun state2 () (_ BitVec 32))
(declare-fun state3 () (_ BitVec 32))
(declare-fun state4 () (_ BitVec 32))

(assert (= (rand state1) state2))
(assert (= (rand state2) state3))
(assert (= (rand state3) state4))

(declare-fun get_result ((_ BitVec 32)) (_ BitVec 32))
(assert (forall ((x (_ BitVec 32)))
        (= (get_result x) (bvurem (bvand (bvlshr x (_ bv16 32)) #x00007fff) (_ bv1000 32)))))

(assert (= (get_result state2) (_ bv0 32)))
(assert (= (get_result state3) (_ bv0 32)))
(assert (= (get_result state4) (_ bv0 32)))

(check-sat)
(get-model)
