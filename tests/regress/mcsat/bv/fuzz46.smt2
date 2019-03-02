(set-logic QF_BV)
(declare-fun _substvar_113_ () (_ BitVec 16))
(declare-fun _substvar_117_ () (_ BitVec 12))
(assert (let ((e4 (bvor (_ bv0 16) ((_ zero_extend 4) _substvar_117_)))) (let ((e10 e4)) (let ((e11 _substvar_117_)) (let ((e17 (ite (bvule _substvar_113_ (_ bv0 16)) (_ bv1 1) (_ bv0 1)))) (let ((e20 ((_ rotate_left 0) e17))) (let ((e26 (distinct ((_ sign_extend 3) e17) (_ bv0 4)))) (let ((e30 (bvugt e11 ((_ sign_extend 11) e20)))) (let ((e71 e26)) (let ((e77 (= true e71))) (let ((e89 (xor e30 e77))) (let ((e105 (xor true e89))) (let ((e106 e105)) (let ((e107 (and e106 (not (= e10 (_ bv0 16)))))) (let ((e108 e107)) e108)))))))))))))))
(check-sat)

