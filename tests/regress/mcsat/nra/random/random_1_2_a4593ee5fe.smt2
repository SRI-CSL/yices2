(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 1))
(let ((e3 (+ v1 v1)))
(let ((e4 (+ v0 v0)))
(let ((e5 (/ e2 e2)))
(let ((e6 (= e5 e4)))
(let ((e7 (<= v1 e5)))
(let ((e8 (< v0 e4)))
(let ((e9 (distinct v0 e4)))
(let ((e10 (distinct e3 e5)))
(let ((e11 (< v1 v0)))
(let ((e12 (<= v0 e3)))
(let ((e13 (> e5 v1)))
(let ((e14 (>= e4 e5)))
(let ((e15 
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
)))
e15
)))))))))))))))

(check-sat)
