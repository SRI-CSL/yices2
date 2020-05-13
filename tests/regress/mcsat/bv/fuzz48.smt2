(set-logic QF_BV)
(declare-fun _substvar_33_ () (_ BitVec 16))
(declare-fun _substvar_46_ () (_ BitVec 10))
(assert (let ((e10 (bvule _substvar_33_ (_ bv0 16)))) (let ((e12 (bvult (_ bv0 10) _substvar_46_))) (let ((e15 (bvuge ((_ sign_extend 6) _substvar_46_) _substvar_33_))) (let ((e19 (= true e12))) (let ((e22 (= e10 false))) (let ((e23 (= false e22))) (let ((e25 (xor e15 e19))) (let ((e26 (not e23))) (let ((e27 e25)) (let ((e28 (and e27 e26))) e28)))))))))))
(check-sat)

