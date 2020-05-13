(set-logic QF_UFBV)
(declare-fun _substvar_112_ () (_ BitVec 8))
(declare-fun _substvar_118_ () (_ BitVec 3))
(declare-fun _substvar_1707_ () Bool)
(declare-fun p0 ((_ BitVec 17) (_ BitVec 7)) Bool)
(assert (let ((e12 (_ bv1 1))) (let ((e20 ((_ zero_extend 2) e12))) (let ((e23 (bvsub (_ bv0 3) e20))) (let ((e29 (bvsrem _substvar_118_ e20))) (let ((e30 (ite (bvsge e29 (_ bv0 3)) (_ bv1 1) (_ bv0 1)))) (let ((e45 (bvule _substvar_112_ ((_ sign_extend 7) e30)))) (let ((e47 (p0 ((_ zero_extend 14) e23) (_ bv0 7)))) (let ((e60 (p0 (_ bv0 17) (_ bv0 7)))) (let ((e83 (bvsgt (_ bv0 1) e30))) (let ((e147 (and e45 e83))) (let ((e149 (= e60 false))) (let ((e150 (or e147 e47))) (let ((e161 (not e150))) (let ((e167 (ite e149 e161 true))) (let ((e184 (xor true _substvar_1707_))) (let ((e186 e167)) (let ((e187 (= e186 false))) (let ((e191 (or e184 e184))) (let ((e197 (not e187))) (let ((e201 (=> e197 false))) (let ((e203 (xor false e201))) (let ((e204 (xor e203 false))) (let ((e206 (=> e204 e191))) (let ((e207 e206)) (let ((e208 (= e207 false))) (let ((e209 e208)) (let ((e210 e209)) e210))))))))))))))))))))))))))))
(check-sat)

