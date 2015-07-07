(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 7))
(let ((e3 3))
(let ((e4 (- v0 v1)))
(let ((e5 (* e4 e4)))
(let ((e6 (* e5 e5)))
(let ((e7 (/ e2 (- e3))))
(let ((e8 (<= e4 v1)))
(let ((e9 (>= e5 e6)))
(let ((e10 (= e6 e6)))
(let ((e11 (> v0 e5)))
(let ((e12 (= e6 v1)))
(let ((e13 (= e6 e4)))
(let ((e14 (distinct e4 e7)))
(let ((e15 (<= e5 e6)))
(let ((e16 (< e6 e7)))
(let ((e17 (<= e4 e5)))
(let ((e18 (distinct e4 v1)))
(let ((e19 (>= v0 e7)))
(let ((e20 
(and
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
 e19
)))
e20
))))))))))))))))))))

(check-sat)
