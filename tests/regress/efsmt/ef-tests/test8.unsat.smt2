;; test8.unsat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (< x y))
(assert (forall ((z Real)) (=> (> y z) (> x z))))
(check-sat)

