(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 5))
(let ((e3 (* v1 (- e2))))
(let ((e4 (- v0)))
(let ((e5 (< e4 e3)))
(let ((e6 (= e3 e4)))
(let ((e7 (> e4 v1)))
(let ((e8 (> v0 e3)))
(let ((e9 (<= v1 v0)))
(let ((e10 (= v0 v0)))
(let ((e11 (distinct e4 v1)))
(let ((e12 (< v1 v0)))
(let ((e13 (> v1 e3)))
(let ((e14 
(and
 e5
 e6
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
