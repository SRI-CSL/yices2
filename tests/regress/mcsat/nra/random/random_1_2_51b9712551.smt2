(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 2))
(let ((e3 (* v0 v0)))
(let ((e4 (/ e2 (- e2))))
(let ((e5 (* e3 v1)))
(let ((e6 (distinct e3 e5)))
(let ((e7 (<= e3 v1)))
(let ((e8 (distinct e3 e5)))
(let ((e9 (< v0 e3)))
(let ((e10 (>= v1 v1)))
(let ((e11 (> v1 e3)))
(let ((e12 (>= e3 e4)))
(let ((e13 (> v0 e4)))
(let ((e14 (distinct v0 e3)))
(let ((e15 (= e5 v0)))
(let ((e16 (>= e5 v0)))
(let ((e17 (distinct v1 e3)))
(let ((e18 
(and
 e6
 e7
 e8
 e9
 e10
 e11
 e12
 e13
 e14
 e15
 e16
 e17
)))
e18
))))))))))))))))))

(check-sat)
