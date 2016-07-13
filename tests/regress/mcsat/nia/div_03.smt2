(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= x y))
(assert (not (= (div x 0) (div y 0))))

(check-sat)
(exit)
