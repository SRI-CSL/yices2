(set-logic QF_BV)
(declare-fun _substvar_31_ () (_ BitVec 15))
(declare-fun _substvar_33_ () (_ BitVec 3))
(declare-fun _substvar_35_ () (_ BitVec 3))
(assert (let ((e4 ((_ rotate_left 1) _substvar_35_))) (let ((e7 (concat _substvar_33_ _substvar_35_))) (let ((e14 (bvugt ((_ sign_extend 4) _substvar_33_) (_ bv0 7)))) (let ((e20 (bvult (_ bv0 15) _substvar_31_))) (let ((e25 (= _substvar_31_ ((_ zero_extend 12) e4)))) (let ((e36 (= false e25))) (let ((e37 (xor e20 false))) (let ((e39 e37)) (let ((e44 (ite e14 e39 false))) (let ((e47 (= true e36))) (let ((e55 (= false e47))) (let ((e56 (=> true e44))) (let ((e57 (xor e56 false))) (let ((e58 (= e57 e55))) (let ((e59 (and e58 (not (= e7 (_ bv0 6)))))) (let ((e60 (and e59 (not (= e7 (_ bv0 6)))))) e60)))))))))))))))))
(check-sat)

