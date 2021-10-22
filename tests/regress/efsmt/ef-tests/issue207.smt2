;; test2.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (forall ((y Real)) (=> (> y 0) (>= y x))))
(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(get-value (x (+ x 10)))
(exit)
