(set-logic QF_BV)
(declare-fun _substvar_22_ () (_ BitVec 16))
(declare-fun _substvar_33_ () (_ BitVec 16))
(assert (let ((e3 (ite (bvult _substvar_22_ _substvar_33_) (_ bv1 1) (_ bv0 1)))) (let ((e6 (distinct ((_ zero_extend 14) e3) (_ bv0 15)))) (let ((e9 (bvugt _substvar_33_ ((_ zero_extend 15) e3)))) (let ((e11 (ite e6 false e9))) (let ((e12 e11)) (let ((e14 (= true e12))) e14)))))))
(check-sat)

