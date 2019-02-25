(set-logic QF_BV)
(declare-fun _substvar_18_ () (_ BitVec 15))
(declare-fun _substvar_27_ () (_ BitVec 15))
(declare-fun _substvar_34_ () (_ BitVec 15))
(assert (let ((e3 (_ bv195 9))) (let ((e4 (bvudiv _substvar_18_ _substvar_34_))) (let ((e6 (bvsdiv ((_ zero_extend 6) e3) e4))) (let ((e17 (bvugt _substvar_27_ e6))) (let ((e26 (= e4 _substvar_27_))) (let ((e27 (bvsle (_ bv0 15) e4))) (let ((e30 (ite e17 e27 true))) (let ((e37 e30)) (let ((e39 e37)) (let ((e40 e26)) (let ((e44 (= true e40))) (let ((e45 (and e44 e39))) (let ((e46 e45)) (let ((e47 e46)) (let ((e48 e47)) e48))))))))))))))))
(check-sat)

