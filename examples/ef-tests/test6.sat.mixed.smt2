;; test6.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (exists ((y Real)) (forall ((z Real)) (=> (> y z) (> x z)))))
(check-sat)
(get-model)
