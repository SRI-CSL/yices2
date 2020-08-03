(set-option :produce-unsat-model-interpolants true)
(set-logic QF_NIA)
(declare-fun v0 () Int)
(assert (let ((e1 44))
(let ((e2 (- v0 v0)))
(let ((e3 (- v0)))
(let ((e4 (* e3 v0)))
(let ((e5 (- v0 e2)))
(let ((e6 (* e1 e5)))
(let ((e7 (distinct e4 e5)))
(let ((e8 (distinct v0 e4)))
(let ((e9 (distinct e6 e5)))
(let ((e10 (= e3 e4)))
(let ((e11 (< e2 e4)))
(let ((e12 (ite e8 e6 e5)))
(let ((e13 (ite e8 e3 v0)))
(let ((e14 (ite e10 e2 e5)))
(let ((e15 (ite e9 e4 v0)))
(let ((e16 (ite e11 e14 v0)))
(let ((e17 (ite e10 e5 e12)))
(let ((e18 (ite e7 e17 e15)))
(let ((e19 (>= e13 e6)))
(let ((e20 (<= e5 e5)))
(let ((e21 (< e15 e12)))
(let ((e22 (> e15 e6)))
(let ((e23 (distinct e6 e2)))
(let ((e24 (> e6 e2)))
(let ((e25 (> e14 v0)))
(let ((e26 (<= e18 e16)))
(let ((e27 (>= e5 e2)))
(let ((e28 (> e5 e12)))
(let ((e29 (> e12 e5)))
(let ((e30 (= e13 e12)))
(let ((e31 (>= e3 e14)))
(let ((e32 (>= e14 e4)))
(let ((e33 (distinct e15 e17)))
(let ((e34
(and
 e7
 e8
 e9
 e10
 e11
 e19
 e20
 e21
 e22
 e23
 e24
 e25
 e26
 e27
 e28
 e29
 e30
 e31
 e32
 e33
)))
e34
)))))))))))))))))))))))))))))))))))
(check-sat-assuming-model (v0) ((- 58)))
(get-unsat-model-interpolant)
