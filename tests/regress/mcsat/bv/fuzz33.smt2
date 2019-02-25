(set-logic QF_BV)
(declare-fun _substvar_105_ () (_ BitVec 15))
(declare-fun _substvar_2087_ () (_ BitVec 15))
(assert (let ((e10 (ite (bvsge _substvar_105_ _substvar_2087_) (_ bv1 1) (_ bv0 1)))) (let ((e33 (ite (bvugt ((_ zero_extend 11) e10) (_ bv0 12)) (_ bv1 1) (_ bv0 1)))) (let ((e59 (bvsge ((_ sign_extend 14) e33) (_ bv0 15)))) (let ((e98 (distinct e10 (_ bv0 1)))) (let ((e144 (=> e98 false))) (let ((e169 e144)) (let ((e218 e169)) (let ((e222 (xor true e218))) (let ((e223 (xor e222 false))) (let ((e225 (and e59 e59))) (let ((e229 (xor e223 true))) (let ((e230 e229)) (let ((e231 (=> e230 e225))) (let ((e233 (xor e231 false))) (let ((e234 (xor e233 true))) (let ((e235 e234)) (let ((e236 e235)) (let ((e237 e236)) (let ((e238 e237)) (let ((e239 e238)) (let ((e240 e239)) e240))))))))))))))))))))))
(check-sat)

