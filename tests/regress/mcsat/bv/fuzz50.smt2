(set-logic QF_BV)
(declare-fun _substvar_70_ () (_ BitVec 13))
(declare-fun _substvar_180_ () (_ BitVec 7))
(declare-fun _substvar_184_ () (_ BitVec 13))
(declare-fun _substvar_2292_ () (_ BitVec 10))
(assert (let ((e7 (bvand _substvar_70_ _substvar_184_))) (let ((e19 (ite (bvsge (_ bv0 13) _substvar_184_) (_ bv1 1) (_ bv0 1)))) (let ((e23 ((_ repeat 1) e7))) (let ((e31 (bvsub (_ bv0 7) _substvar_180_))) (let ((e47 (ite (= (_ bv1 1) ((_ extract 0 0) e19)) _substvar_2292_ (_ bv0 10)))) (let ((e60 (bvsge _substvar_180_ (_ bv0 7)))) (let ((e71 (= (_ bv0 13) e23))) (let ((e107 (= e47 ((_ sign_extend 3) e31)))) (let ((e164 (xor false e71))) (let ((e185 e107)) (let ((e215 (xor e185 true))) (let ((e216 (xor e60 false))) (let ((e234 (ite e216 e164 false))) (let ((e239 (or e234 e215))) (let ((e252 e239)) (let ((e253 (and e252 e252))) (let ((e254 (or e253 e253))) (let ((e255 (=> e254 false))) (let ((e256 e255)) (let ((e257 e256)) (let ((e258 e257)) (let ((e259 (and e258 (not (= _substvar_180_ (_ bv0 7)))))) e259)))))))))))))))))))))))
(check-sat)

