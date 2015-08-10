;; test8.unsat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (exists ((y Real)) (and (< x y) (forall ((z Real)) (=> (> y z) (> x z))))))
(check-sat)

