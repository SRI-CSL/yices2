(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 10))
(declare-fun v1 () (_ BitVec 13))
(declare-fun v2 () (_ BitVec 15))
(assert 
(let ((e3 (_ bv7993 13)))
(let ((e4 (ite (= v1 ((_ sign_extend 3) v0)) (_ bv1 1) (_ bv0 1))))
(let ((e7 (= ((_ sign_extend 12) e4) v1)))
(let ((e10 (= v2 ((_ zero_extend 2) e3))))
(let ((e11 
(and
 e7
 e10
)))
e11
))))))

(check-sat)
