(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 1))
(let ((e3 (- v0 v0)))
(let ((e4 (- v0)))
(let ((e5 (* (- e2) e3)))
(let ((e6 (- v1 e3)))
(let ((e7 (> e4 e5)))
(let ((e8 (= v1 v0)))
(let ((e9 (< e6 e5)))
(let ((e10 (distinct e6 e5)))
(let ((e11 (= v0 v1)))
(let ((e12 (>= v0 v0)))
(let ((e13 (>= e4 v1)))
(let ((e14 (< v1 e3)))
(let ((e15 (= e5 e3)))
(let ((e16 (> v1 v0)))
(let ((e17 (distinct e3 e4)))
(let ((e18 (<= e6 v1)))
(let ((e19 
(and
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
 e18
)))
e19
)))))))))))))))))))

(check-sat)
