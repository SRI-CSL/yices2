;; converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)

(assert (exists ((y Real) (z Real)) (forall ((t Real)) (distinct x y z t))))
(check-sat)
