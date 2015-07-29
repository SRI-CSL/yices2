;;  test1.unsat.ys converted to the SMT-LIB2 notation
(set-logic LRA)


(declare-fun x () Real)
(assert (forall ((y Real)) (> x y)))
(check-sat)
(exit)

