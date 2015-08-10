;; test9.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(assert (exists ((z Real)) (forall ((t Real)) (or (distinct x y t) (distinct x z t) (distinct y z t)))))
(check-sat)
(get-model)
