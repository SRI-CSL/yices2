(set-logic QF_BV)
(declare-fun _substvar_111_ () (_ BitVec 15))
(declare-fun _substvar_112_ () (_ BitVec 15))
(assert (let ((e4 (bvnot (_ bv0 7)))) (let ((e6 (bvlshr ((_ zero_extend 8) e4) _substvar_111_))) (let ((e9 ((_ repeat 1) e6))) (let ((e24 (ite (bvsge _substvar_112_ (_ bv0 15)) (_ bv1 1) (_ bv0 1)))) (let ((e25 (bvsub (_ bv0 15) e6))) (let ((e61 (bvugt e9 (_ bv0 15)))) (let ((e85 (distinct (_ bv0 1) e24))) (let ((e87 (bvugt ((_ sign_extend 14) e24) e25))) (let ((e96 (not e61))) (let ((e106 e96)) (let ((e108 (xor true e87))) (let ((e123 (not e106))) (let ((e131 (xor e85 false))) (let ((e133 (ite e108 e123 false))) (let ((e142 (=> e133 false))) (let ((e143 (=> true e142))) (let ((e144 (ite e143 false e131))) (let ((e146 (xor e144 false))) e146)))))))))))))))))))
(check-sat)

