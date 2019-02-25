(set-logic QF_BV)
(declare-fun _substvar_64_ () (_ BitVec 7))
(declare-fun _substvar_98_ () (_ BitVec 5))
(assert (let ((e6 (bvurem _substvar_64_ _substvar_64_))) (let ((e7 (ite (= (_ bv1 1) ((_ extract 5 5) e6)) (_ bv0 7) e6))) (let ((e11 (ite (distinct (_ bv0 14) ((_ zero_extend 9) _substvar_98_)) (_ bv1 1) (_ bv0 1)))) (let ((e17 (bvsub ((_ sign_extend 13) e11) (_ bv0 14)))) (let ((e75 (bvslt e7 ((_ zero_extend 6) e11)))) (let ((e84 (bvsgt (_ bv0 14) e17))) (let ((e89 (xor false e84))) (let ((e98 (and e89 e75))) (let ((e121 (not e98))) (let ((e122 (ite e121 true false))) (let ((e127 (=> e122 false))) (let ((e131 (xor e127 false))) (let ((e140 e131)) (let ((e142 (= e140 false))) (let ((e146 (or e142 e142))) (let ((e147 e146)) (let ((e148 (and e147 (not (= _substvar_98_ (_ bv0 5)))))) (let ((e149 e148)) (let ((e150 (and e149 (not (= _substvar_64_ (_ bv0 7)))))) e150))))))))))))))))))))
(check-sat)

