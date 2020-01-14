(set-logic QF_BV)
(declare-fun _substvar_29_ () (_ BitVec 14))
(declare-fun _substvar_34_ () (_ BitVec 14))
(declare-fun _substvar_36_ () (_ BitVec 2))
(declare-fun _substvar_42_ () (_ BitVec 13))
(assert (let ((e4 (ite (bvugt ((_ sign_extend 1) _substvar_42_) _substvar_34_) (_ bv1 1) (_ bv0 1)))) (let ((e8 (bvuge _substvar_34_ _substvar_29_))) (let ((e10 (bvuge (_ bv0 14) _substvar_34_))) (let ((e11 (bvslt ((_ sign_extend 1) e4) _substvar_36_))) (let ((e12 (bvule _substvar_34_ (_ bv0 14)))) (let ((e13 (= (_ bv0 2) _substvar_36_))) (let ((e14 (bvuge _substvar_36_ ((_ sign_extend 1) e4)))) (let ((e16 (xor e12 e14))) (let ((e17 (or e10 e10))) (let ((e18 (ite e17 true e8))) (let ((e19 (xor e13 e18))) (let ((e20 (ite e16 e11 e16))) (let ((e21 e20)) (let ((e22 (not e19))) (let ((e23 (xor e22 e21))) (let ((e24 (and e23 (not (= _substvar_42_ (_ bv0 13)))))) e24)))))))))))))))))
(check-sat)

