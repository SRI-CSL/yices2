(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(assert (let ((e1 1))
(let ((e2 (* v0 v0)))
(let ((e3 (/ e1 e1)))
(let ((e4 (= v0 e3)))
(let ((e5 (< e2 v0)))
(let ((e6 (<= e3 e3)))
(let ((e7 (= e2 v0)))
(let ((e8 
(and
 e4
 e5
 e6
 e7
)))
e8
)))))))))

(check-sat)
