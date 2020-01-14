(set-logic QF_BV)
(declare-fun _substvar_81_ () (_ BitVec 14))
(declare-fun _substvar_83_ () (_ BitVec 14))
(declare-fun _substvar_2033_ () Bool)
(assert (let ((e19 (bvsub (_ bv0 14) _substvar_81_))) (let ((e20 (bvor (_ bv0 14) e19))) (let ((e26 (ite (bvsle _substvar_83_ _substvar_81_) (_ bv1 1) (_ bv0 1)))) (let ((e34 (ite _substvar_2033_ e20 (_ bv0 14)))) (let ((e57 (bvuge (_ bv0 1) e26))) (let ((e213 (xor false e57))) (let ((e236 (=> true e213))) (let ((e246 (not e236))) (let ((e251 e246)) (let ((e253 (not e251))) (let ((e254 e253)) (let ((e255 (and e254 (not (= e34 (_ bv0 14)))))) (let ((e256 (and e255 (not (= e34 (bvnot (_ bv0 14))))))) (let ((e257 e256)) (let ((e258 (and e257 (not (= _substvar_81_ (_ bv0 14)))))) (let ((e259 e258)) (let ((e260 e259)) e260))))))))))))))))))
(check-sat)

