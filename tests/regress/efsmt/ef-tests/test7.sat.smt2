;; test7.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (not (= x y)))
(assert (forall ((z Real)) (=> (> y z) (> x z))))
(check-sat)
