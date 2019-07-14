(set-logic QF_UFBV)
(declare-fun p0 ((_ BitVec 21) (_ BitVec 13)) Bool)
(assert (let ((e1 (_ bv1 2))) (let ((e2 (_ bv673 10))) (let ((e4 (ite (p0 (_ bv0 21) ((_ zero_extend 3) e2)) (_ bv1 1) (_ bv0 1)))) (let ((e7 (bvsrem ((_ sign_extend 1) e4) e1))) (let ((e8 (= (_ bv0 2) e7))) (let ((e12 (p0 (_ bv0 21) (_ bv0 13)))) (let ((e14 (not e8))) (let ((e15 (= true e12))) (let ((e17 (ite e14 true false))) (let ((e18 (or e15 e17))) (let ((e19 e18)) (let ((e20 e19)) e20)))))))))))))
(check-sat)

