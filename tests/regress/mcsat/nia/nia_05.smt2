(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x 0))
(assert (> y 0))
(assert (> z 0))

(assert (= (* z z) (+ (* x x) (* y y))))

(check-sat)

(exit)
