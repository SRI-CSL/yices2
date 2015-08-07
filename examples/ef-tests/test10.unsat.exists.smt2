;; converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (exists ((x Real) (y Real) (z Real)) (forall ((t Real)) (distinct x y z t))))
(check-sat)
