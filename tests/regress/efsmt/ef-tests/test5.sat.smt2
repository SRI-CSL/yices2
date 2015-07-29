;; test5.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(assert (forall ((y Real)) (or (not (= x y)) (= y 100))))
(check-sat)
