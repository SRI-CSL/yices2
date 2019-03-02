(set-logic QF_BV)
(declare-fun _substvar_90_ () (_ BitVec 9))
(declare-fun _substvar_91_ () (_ BitVec 9))
(declare-fun _substvar_100_ () (_ BitVec 4))
(assert (let ((e12 (bvurem ((_ zero_extend 5) _substvar_100_) _substvar_91_))) (let ((e30 (bvule _substvar_90_ (_ bv0 9)))) (let ((e42 (bvsge e12 (_ bv0 9)))) (let ((e67 (bvugt ((_ sign_extend 5) _substvar_100_) _substvar_90_))) (let ((e108 e42)) (let ((e116 (= false e108))) (let ((e138 e116)) (let ((e153 e67)) (let ((e159 e153)) (let ((e162 (ite e159 e159 e138))) (let ((e166 (=> true e162))) (let ((e167 e166)) (let ((e168 e167)) (let ((e169 e168)) (let ((e170 e169)) (let ((e171 e170)) (let ((e172 e171)) (let ((e173 (and e172 (not (= _substvar_90_ (_ bv0 9)))))) (let ((e174 e173)) e174))))))))))))))))))))
(check-sat)

