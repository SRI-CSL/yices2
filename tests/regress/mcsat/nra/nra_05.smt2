(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (= (* x x) 2))
(assert (= (* y y) 3))
(assert (= x y)) 

(check-sat)
(exit)
