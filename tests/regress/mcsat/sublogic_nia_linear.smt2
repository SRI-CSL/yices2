(set-logic QF_NIA)
; Linear problem declared in a non-linear logic: solved with the simplex solver
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (+ x y) 3))
(assert (< x 2))
(assert (= (mod y 3) 1))
(check-sat)
