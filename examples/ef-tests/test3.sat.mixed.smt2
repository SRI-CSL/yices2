;; test3.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real)) (forall ((y Real)) (=> (> y 0) (< x y)))))
(check-sat)
(get-model)

