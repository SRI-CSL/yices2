;; test3.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (forall ((y Real)) (=> (> y 0) (< x y))))
(check-sat)

