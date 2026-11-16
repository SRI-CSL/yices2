(set-logic QF_NIA)
; Truly non-linear problem: stays in QF_NIA
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 12))
(assert (> x 2))
(assert (> y 2))
(check-sat)
