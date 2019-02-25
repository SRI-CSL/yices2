(set-logic QF_BV)
(declare-fun _substvar_68_ () (_ BitVec 16))
(declare-fun _substvar_87_ () (_ BitVec 10))
(declare-fun _substvar_90_ () (_ BitVec 14))
(assert (let ((e20 (bvnand _substvar_90_ ((_ sign_extend 4) _substvar_87_)))) (let ((e86 (bvule ((_ sign_extend 6) _substvar_87_) _substvar_68_))) (let ((e114 (distinct e20 (_ bv0 14)))) (let ((e127 e114)) (let ((e155 e86)) (let ((e156 e127)) (let ((e189 (xor e156 false))) (let ((e193 e189)) (let ((e202 (not e155))) (let ((e203 e202)) (let ((e205 e203)) (let ((e207 (= e205 true))) (let ((e208 (and e207 e193))) (let ((e209 e208)) (let ((e210 e209)) (let ((e211 e210)) (let ((e212 e211)) (let ((e213 e212)) (let ((e214 (and e213 (not (= _substvar_68_ (_ bv0 16)))))) e214))))))))))))))))))))
(check-sat)

