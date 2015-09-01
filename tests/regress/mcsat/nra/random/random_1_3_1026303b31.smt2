(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(assert (let ((e3 2))
(let ((e4 4))
(let ((e5 (/ e4 e3)))
(let ((e6 (* e5 e5)))
(let ((e7 (* v2 v2)))
(let ((e8 (- v1)))
(let ((e9 (/ e3 (- e3))))
(let ((e10 (- e7)))
(let ((e11 (+ v0 e9)))
(let ((e12 (<= e10 e11)))
(let ((e13 (distinct e5 v1)))
(let ((e14 (> e7 e11)))
(let ((e15 (>= v2 e9)))
(let ((e16 (<= e8 v0)))
(let ((e17 (<= v0 e8)))
(let ((e18 (< e8 e9)))
(let ((e19 (<= e6 v2)))
(let ((e20 (= v0 e8)))
(let ((e21 (> e7 e6)))
(let ((e22 (<= e10 v0)))
(let ((e23 (> e5 v1)))
(let ((e24 (< v0 e9)))
(let ((e25 (<= e10 e6)))
(let ((e26 (distinct e9 e6)))
(let ((e27 (< v2 e11)))
(let ((e28 
(and
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
)))
e28
)))))))))))))))))))))))))))

(check-sat)
