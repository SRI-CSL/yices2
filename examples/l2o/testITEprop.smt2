(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun w () Real)

(assert (ite (= x y) (= 0 x) (= 0 w)))

(assert (= (+ (* z z) (* w w)) 1))
(assert (>= (+ (* (- x z) (- x z)) (* (- y w) (- y w))) 1))
(check-sat)