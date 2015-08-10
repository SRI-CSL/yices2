;;  test1.unsat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (exists ((z Real)) (forall ((y Real)) (and (> x y) (> z y)))))
(check-sat)
(exit)

