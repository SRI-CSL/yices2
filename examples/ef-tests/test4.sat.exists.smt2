;; test4.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real)) (forall ((y Real)) (or (not (= x y)) (= y 0)))))
(check-sat)
(get-model)
