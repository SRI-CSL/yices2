(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 4))
(let ((e3 (* v0 v1)))
(let ((e4 (+ e3 v0)))
(let ((e5 (/ e2 e2)))
(let ((e6 (<= v0 e3)))
(let ((e7 (>= e4 e4)))
(let ((e8 (>= e5 e3)))
(let ((e9 (>= v0 v1)))
(let ((e10 (>= e5 e4)))
(let ((e11 (>= e3 e3)))
(let ((e12 (= v1 e3)))
(let ((e13 (>= e5 v1)))
(let ((e14 (distinct v0 e3)))
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
