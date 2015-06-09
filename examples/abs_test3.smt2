(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> (abs x) x))
(check-sat)
(get-model)
(get-value (x (abs x)))

