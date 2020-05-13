(set-logic QF_BV)
(declare-fun _substvar_19_ () (_ BitVec 14))
(declare-fun _substvar_106_ () Bool)
(assert (let ((e5 _substvar_19_)) (let ((e8 (ite _substvar_106_ e5 (_ bv0 14)))) (let ((e14 (bvslt e5 e8))) (let ((e18 (bvsle _substvar_19_ (_ bv0 14)))) (let ((e24 e18)) (let ((e26 (= e14 e24))) (let ((e29 (= true e26))) (let ((e31 (xor false e29))) e31)))))))))
(check-sat)

