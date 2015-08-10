;; converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real) (y Real) (z Real)) (forall ((t Real)) (distinct x y z t))))
(check-sat)
