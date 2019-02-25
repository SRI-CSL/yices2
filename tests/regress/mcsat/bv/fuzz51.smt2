(set-logic QF_BV)
(declare-fun _substvar_47_ () (_ BitVec 16))
(declare-fun _substvar_50_ () (_ BitVec 16))
(assert (let ((e8 (ite (bvult (_ bv0 16) _substvar_50_) (_ bv1 1) (_ bv0 1)))) (let ((e13 (ite (bvugt _substvar_47_ (_ bv0 16)) (_ bv1 1) (_ bv0 1)))) (let ((e14 (= e13 (_ bv0 1)))) (let ((e17 (bvugt e13 e8))) (let ((e26 (bvult (_ bv0 16) _substvar_50_))) (let ((e43 (or e17 e14))) (let ((e47 (not e43))) (let ((e49 (and e47 e47))) (let ((e50 e49)) (let ((e52 e26)) (let ((e53 (= e52 e50))) (let ((e56 (and e53 e53))) (let ((e58 (= false e56))) e58))))))))))))))
(check-sat)

