(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 2))
(let ((e3 (- v0 v1)))
(let ((e4 (* e3 e3)))
(let ((e5 (- v1)))
(let ((e6 (- e3)))
(let ((e7 (- e4)))
(let ((e8 (- e3 v1)))
(let ((e9 (- v1)))
(let ((e10 (/ e2 e2)))
(let ((e11 (>= e6 e4)))
(let ((e12 (< e10 e6)))
(let ((e13 (< e5 v1)))
(let ((e14 (>= v1 e5)))
(let ((e15 (> e7 e9)))
(let ((e16 (>= e9 e8)))
(let ((e17 (< e8 e6)))
(let ((e18 (>= e8 e10)))
(let ((e19 (>= e9 e9)))
(let ((e20 (= e7 e9)))
(let ((e21 (distinct e3 v0)))
(let ((e22 (distinct v1 e8)))
(let ((e23 (<= e4 e10)))
(let ((e24 (distinct e10 e3)))
(let ((e25 (< v0 v1)))
(let ((e26 (< e6 e7)))
(let ((e27 (> e3 e5)))
(let ((e28 (<= e4 e4)))
(let ((e29 (<= e8 e10)))
(let ((e30 (= e9 e6)))
(let ((e31 
(and
 e11
 e12
 e13
 e14
 e15
 e16
 e17
 e18
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
)))
e31
)))))))))))))))))))))))))))))))

(check-sat)
