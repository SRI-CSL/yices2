(set-logic QF_BV)
(declare-fun _substvar_81_ () (_ BitVec 12))
(assert (let ((e5 (ite (bvsle _substvar_81_ (_ bv0 12)) (_ bv1 1) (_ bv0 1)))) (let ((e9 (concat e5 (_ bv0 13)))) (let ((e11 (bvxor e9 (_ bv0 14)))) (let ((e23 (bvugt e5 (_ bv0 1)))) (let ((e50 (bvslt e11 (_ bv0 14)))) (let ((e68 e50)) (let ((e78 (=> true e23))) (let ((e82 e78)) (let ((e84 (not e82))) (let ((e86 e84)) (let ((e87 (= e86 true))) (let ((e88 (= e87 e68))) (let ((e89 e88)) (let ((e90 e89)) (let ((e91 e90)) e91))))))))))))))))
(check-sat)

