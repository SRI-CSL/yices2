(set-logic QF_BV)
(declare-fun _substvar_25_ () (_ BitVec 9))
(declare-fun _substvar_26_ () (_ BitVec 16))
(assert (let ((e2 (_ bv4783 16))) (let ((e3 (ite (bvsge ((_ sign_extend 7) _substvar_25_) _substvar_26_) (_ bv1 1) (_ bv0 1)))) (let ((e4 (bvmul ((_ zero_extend 15) e3) e2))) (let ((e8 (bvslt ((_ sign_extend 7) _substvar_25_) _substvar_26_))) (let ((e11 (bvsle (_ bv0 16) e4))) (let ((e12 (= false e8))) (let ((e16 (or e12 e11))) (let ((e17 (ite e16 false true))) e17)))))))))
(check-sat)

