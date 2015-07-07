(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 2))
(let ((e3 2))
(let ((e4 (+ v0 v1)))
(let ((e5 (- v0)))
(let ((e6 (/ e2 e3)))
(let ((e7 (> e6 e5)))
(let ((e8 (<= v1 v0)))
(let ((e9 (<= v0 e4)))
(let ((e10 (> e5 v1)))
(let ((e11 (<= e5 e4)))
(let ((e12 (< v0 e4)))
(let ((e13 (distinct e6 e4)))
(let ((e14 
(and
 e7
 e8
 e9
 e10
 e11
 e12
 e13
)))
e14
))))))))))))))

(check-sat)
