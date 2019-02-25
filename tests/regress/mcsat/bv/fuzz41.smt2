(set-logic QF_BV)
(declare-fun _substvar_69_ () (_ BitVec 8))
(declare-fun _substvar_72_ () (_ BitVec 8))
(assert (let ((e4 (_ bv33145 16))) (let ((e5 (bvcomp _substvar_72_ _substvar_69_))) (let ((e36 (bvmul e4 ((_ sign_extend 15) e5)))) (let ((e44 (bvslt e36 e4))) (let ((e137 e44)) (let ((e202 e137)) (let ((e203 e202)) (let ((e204 e203)) (let ((e205 e204)) (let ((e206 e205)) (let ((e207 (and e206 (not (= e5 (_ bv0 1)))))) (let ((e208 e207)) e208)))))))))))))
(check-sat)

