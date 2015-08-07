;; test2.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real)) (forall ((y Real)) (=> (> y 0) (>= y x)))))
(check-sat)
(get-model)
