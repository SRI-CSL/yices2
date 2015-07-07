(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 9))
(let ((e3 (* v1 v0)))
(let ((e4 (* (- e2) e3)))
(let ((e5 (> e4 v1)))
(let ((e6 (>= e4 v0)))
(let ((e7 (< e3 v1)))
(let ((e8 (<= v0 v0)))
(let ((e9 (> e3 e4)))
(let ((e10 (<= v1 e4)))
(let ((e11 
(and
 e5
 e6
 e7
 e8
 e9
 e10
)))
e11
)))))))))))

(check-sat)
