;; test5.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real)) (forall ((y Real)) (or (not (= x y)) (= y 100)))))
(check-sat)
(get-model)
