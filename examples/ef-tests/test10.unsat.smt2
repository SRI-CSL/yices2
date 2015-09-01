;; converted to the SMT-LIB2 notation
(set-logic LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (forall ((t Real)) (distinct x y z t)))
(check-sat)
