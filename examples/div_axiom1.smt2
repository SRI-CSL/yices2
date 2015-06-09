(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (<= (* 5 y) x) (< x (+ (* 5 y) 5)) (not (= y (div x 5)))))
(check-sat)
(get-model)

