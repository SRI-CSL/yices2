(set-logic QF_LIA)
(declare-fun x () Int)
(assert (<= x 0))
(assert (> (abs x) 20))
(check-sat)
(get-model)
(get-value (x (abs x)))

