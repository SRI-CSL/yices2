;;  test1.unsat.ys converted to the SMT-LIB2 notation
(set-logic LRA)


(assert (exists ((x Real)) (forall ((y Real)) (> x y))))
(check-sat)
(exit)

