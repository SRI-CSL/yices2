(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 15))
(let ((e3 5))
(let ((e4 (- v0)))
(let ((e5 (* (- e3) v0)))
(let ((e6 (/ e3 e2)))
(let ((e7 (* v1 e5)))
(let ((e8 (> e4 v0)))
(let ((e9 (distinct e6 v0)))
(let ((e10 (< e6 v1)))
(let ((e11 (distinct v1 v0)))
(let ((e12 (<= e5 e7)))
(let ((e13 (> v1 v0)))
(let ((e14 (distinct v1 e4)))
(let ((e15 (distinct e5 v0)))
(let ((e16 (= v0 v0)))
(let ((e17 (distinct e6 e7)))
(let ((e18 
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
)))
e18
))))))))))))))))))

(check-sat)
