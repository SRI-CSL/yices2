(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun w () Real)

(assert (= 0 (ite (= x y) x w)))

(assert (= (+ (* z z) (* w w)) 1))
(assert (>= (+ (* (- x z) (- x z)) (* (- y w) (- y w))) 1))
(check-sat)