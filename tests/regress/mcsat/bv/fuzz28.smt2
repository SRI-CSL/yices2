(set-logic QF_BV)
(declare-fun _substvar_122_ () (_ BitVec 4))
(declare-fun _substvar_126_ () (_ BitVec 16))
(declare-fun _substvar_1465_ () (_ BitVec 14))
(assert (let ((e8 (bvsrem _substvar_122_ _substvar_122_))) (let ((e10 (ite (bvsgt _substvar_1465_ (_ bv0 14)) (_ bv1 1) (_ bv0 1)))) (let ((e15 (_ bv1 1))) (let ((e17 ((_ sign_extend 14) e15))) (let ((e19 (ite (bvuge ((_ sign_extend 10) e8) _substvar_1465_) (_ bv1 1) (_ bv0 1)))) (let ((e27 (= (_ bv0 8) ((_ zero_extend 7) e19)))) (let ((e28 (distinct _substvar_126_ ((_ sign_extend 12) _substvar_122_)))) (let ((e51 (bvugt ((_ zero_extend 1) e17) _substvar_126_))) (let ((e57 (bvuge (_ bv0 1) e10))) (let ((e83 e51)) (let ((e101 e28)) (let ((e106 (=> e27 false))) (let ((e108 (not e83))) (let ((e110 e57)) (let ((e114 (xor e108 e106))) (let ((e116 e114)) (let ((e120 (=> e116 false))) (let ((e125 e101)) (let ((e126 (ite e110 true false))) (let ((e127 (and e126 e125))) (let ((e130 (=> e127 false))) (let ((e132 (and e130 e120))) (let ((e133 e132)) (let ((e134 e133)) (let ((e135 e134)) (let ((e136 e135)) e136)))))))))))))))))))))))))))
(check-sat)

