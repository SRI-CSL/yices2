(set-logic QF_BV)
(declare-fun _substvar_77_ () (_ BitVec 14))
(declare-fun _substvar_92_ () (_ BitVec 14))
(declare-fun _substvar_100_ () (_ BitVec 14))
(assert (let ((e13 (ite (bvsle _substvar_92_ _substvar_100_) (_ bv1 1) (_ bv0 1)))) (let ((e15 (bvnand _substvar_77_ ((_ zero_extend 13) e13)))) (let ((e21 (bvand _substvar_77_ ((_ sign_extend 13) e13)))) (let ((e85 (= e21 (_ bv0 14)))) (let ((e220 (=> e85 false))) (let ((e244 e220)) (let ((e245 e244)) (let ((e248 (not e245))) (let ((e259 (= true e248))) (let ((e260 e259)) (let ((e261 e260)) (let ((e262 (and e261 (not (= e15 (bvnot (_ bv0 14))))))) (let ((e263 e262)) (let ((e264 e263)) e264)))))))))))))))
(check-sat)

