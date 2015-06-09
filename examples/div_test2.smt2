(set-logic QF_LIA)
(declare-fun x () Int)
(assert (< (div x 5) (- 3)))
(check-sat)
(get-model)
(get-value (x (div x 5) (mod x 5)))

