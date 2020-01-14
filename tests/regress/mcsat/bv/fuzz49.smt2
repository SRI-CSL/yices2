(set-logic QF_BV)
(declare-fun _substvar_46_ () (_ BitVec 5))
(declare-fun _substvar_1209_ () Bool)
(assert (let ((e7 (ite (bvslt (_ bv0 5) _substvar_46_) (_ bv1 1) (_ bv0 1)))) (let ((e25 (ite _substvar_1209_ (_ bv0 9) ((_ sign_extend 4) _substvar_46_)))) (let ((e79 (bvsge ((_ zero_extend 8) e7) e25))) (let ((e105 (xor true e79))) (let ((e127 (= true e105))) (let ((e136 (not e127))) (let ((e143 (not e136))) (let ((e148 (xor e143 false))) (let ((e149 (and e148 (not (= _substvar_46_ (_ bv0 5)))))) (let ((e150 e149)) e150)))))))))))
(check-sat)

