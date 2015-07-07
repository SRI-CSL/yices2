(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(assert (let ((e3 7))
(let ((e4 1))
(let ((e5 (- v1 v2)))
(let ((e6 (* e5 v0)))
(let ((e7 (/ e4 (- e3))))
(let ((e8 (>= e5 e6)))
(let ((e9 (distinct v0 e7)))
(let ((e10 (> v1 v2)))
(let ((e11 (> e7 e5)))
(let ((e12 (distinct v1 v0)))
(let ((e13 (= v0 v2)))
(let ((e14 (< e6 e7)))
(let ((e15 
(and
 e8
 e9
 e10
 e11
 e12
 e13
 e14
)))
e15
))))))))))))))

(check-sat)
