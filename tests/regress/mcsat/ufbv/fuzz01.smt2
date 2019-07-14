(set-logic QF_UFBV)
(declare-fun _substvar_102_ () (_ BitVec 1))
(declare-fun _substvar_112_ () (_ BitVec 12))
(declare-fun f1 ((_ BitVec 15) (_ BitVec 1)) (_ BitVec 12))
(declare-fun p1 ((_ BitVec 2)) Bool)
(assert (let ((e8 (f1 (_ bv0 15) (_ bv0 1)))) (let ((e9 (f1 ((_ sign_extend 14) _substvar_102_) (_ bv0 1)))) (let ((e14 (ite (bvule e8 _substvar_112_) (_ bv1 1) (_ bv0 1)))) (let ((e15 (bvnor e14 _substvar_102_))) (let ((e18 (ite (bvslt (_ bv0 12) e9) (_ bv1 1) (_ bv0 1)))) (let ((e24 (ite (bvsgt ((_ sign_extend 11) e18) _substvar_112_) (_ bv1 1) (_ bv0 1)))) (let ((e30 (ite (bvuge (_ bv0 29) ((_ sign_extend 28) e24)) (_ bv1 1) (_ bv0 1)))) (let ((e81 (p1 ((_ zero_extend 1) e30)))) (let ((e106 (=> e81 false))) (let ((e115 e106)) (let ((e125 (xor false e115))) (let ((e143 (or e125 e125))) (let ((e144 (=> e143 false))) (let ((e146 (= e144 false))) (let ((e147 (and e146 (not (= e15 (_ bv0 1)))))) e147))))))))))))))))
(check-sat)

