(set-logic QF_BV)
(declare-fun _substvar_34_ () (_ BitVec 9))
(declare-fun _substvar_74_ () (_ BitVec 9))
(declare-fun _substvar_76_ () (_ BitVec 2))
(declare-fun _substvar_79_ () (_ BitVec 2))
(assert (let ((e4 (ite (distinct _substvar_34_ _substvar_74_) (_ bv1 1) (_ bv0 1)))) (let ((e5 (bvand _substvar_76_ ((_ sign_extend 1) e4)))) (let ((e7 (ite (bvugt _substvar_74_ (_ bv0 9)) (_ bv1 1) (_ bv0 1)))) (let ((e10 (ite (= (_ bv1 1) ((_ extract 0 0) e7)) _substvar_79_ (_ bv0 2)))) (let ((e23 (bvult e10 e5))) (let ((e31 (bvsge ((_ sign_extend 1) e4) _substvar_76_))) (let ((e43 e23)) (let ((e44 (=> true e43))) (let ((e45 (= e31 true))) (let ((e46 e45)) (let ((e48 e44)) (let ((e49 e46)) (let ((e50 (= e49 e48))) (let ((e51 e50)) (let ((e57 (or e51 e51))) (let ((e58 (xor e57 false))) (let ((e59 e58)) (let ((e60 (and e59 (not (= e5 (_ bv0 2)))))) e60)))))))))))))))))))
(check-sat)

