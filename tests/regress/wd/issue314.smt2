(set-logic LRA)
(assert (forall ((x Real)) (exists ((y Real)) (> y x))))
(check-sat)

