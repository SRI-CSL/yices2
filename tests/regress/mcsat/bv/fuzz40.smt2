(set-logic QF_BV)
(declare-fun _substvar_94_ () (_ BitVec 5))
(declare-fun _substvar_109_ () (_ BitVec 5))
(declare-fun _substvar_120_ () (_ BitVec 9))
(declare-fun _substvar_707_ () Bool)
(assert (let ((e7 ((_ sign_extend 9) _substvar_94_))) (let ((e10 (_ bv1 1))) (let ((e16 (bvsub e7 ((_ sign_extend 5) _substvar_120_)))) (let ((e18 (bvashr ((_ zero_extend 13) e10) e16))) (let ((e29 (bvurem _substvar_109_ _substvar_94_))) (let ((e51 (ite _substvar_707_ e18 (_ bv0 14)))) (let ((e142 (distinct e51 ((_ sign_extend 5) _substvar_120_)))) (let ((e172 (bvuge (_ bv0 14) e16))) (let ((e231 (xor false e172))) (let ((e297 (and e142 e231))) (let ((e305 e297)) (let ((e307 (=> true e305))) (let ((e312 (= false e307))) (let ((e313 e312)) (let ((e314 (and e313 (not (= e29 (_ bv0 5)))))) (let ((e315 e314)) (let ((e316 e315)) (let ((e317 e316)) (let ((e318 (and e317 (not (= e51 (_ bv0 14)))))) e318))))))))))))))))))))
(check-sat)

