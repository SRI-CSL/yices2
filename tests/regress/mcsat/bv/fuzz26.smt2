(set-logic QF_BV)
(declare-fun _substvar_20_ () (_ BitVec 3))
(declare-fun _substvar_30_ () (_ BitVec 3))
(assert (let ((e12 (bvule _substvar_30_ _substvar_20_))) (let ((e15 (distinct _substvar_20_ (_ bv0 3)))) (let ((e21 (bvugt ((_ sign_extend 13) _substvar_30_) (_ bv0 16)))) (let ((e34 (xor e21 false))) (let ((e38 (xor true e34))) (let ((e39 e15)) (let ((e45 (= e39 e12))) (let ((e49 (ite e38 true false))) (let ((e50 (or e45 e49))) (let ((e51 (xor e50 true))) e51)))))))))))
(check-sat)

