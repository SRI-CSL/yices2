(set-logic QF_BV)
(declare-fun _substvar_78_ () (_ BitVec 11))
(declare-fun _substvar_83_ () (_ BitVec 10))
(declare-fun _substvar_92_ () (_ BitVec 1))
(declare-fun _substvar_96_ () (_ BitVec 7))
(declare-fun _substvar_769_ () Bool)
(assert (let ((e10 (bvmul ((_ zero_extend 1) _substvar_83_) _substvar_78_))) (let ((e13 (bvcomp _substvar_78_ (_ bv0 11)))) (let ((e15 ((_ sign_extend 0) e10))) (let ((e17 ((_ zero_extend 6) _substvar_92_))) (let ((e20 (bvult ((_ zero_extend 4) e17) _substvar_78_))) (let ((e24 (distinct e13 (_ bv0 1)))) (let ((e25 (bvsge e15 ((_ sign_extend 4) e17)))) (let ((e32 (distinct ((_ sign_extend 6) _substvar_92_) _substvar_96_))) (let ((e35 (bvult (_ bv0 10) _substvar_83_))) (let ((e39 (bvuge (_ bv0 7) _substvar_96_))) (let ((e41 (ite e25 false true))) (let ((e44 (=> e20 e24))) (let ((e45 e41)) (let ((e46 (and e35 _substvar_769_))) (let ((e49 e39)) (let ((e51 e44)) (let ((e52 (not e49))) (let ((e54 (= false e46))) (let ((e56 (or e52 e45))) (let ((e57 (= e32 true))) (let ((e58 (or e57 e51))) (let ((e59 (not e54))) (let ((e60 (=> e56 e58))) (let ((e61 (or e60 e59))) (let ((e62 (= e61 true))) (let ((e63 (not e62))) (let ((e64 e63)) e64))))))))))))))))))))))))))))
(check-sat)

