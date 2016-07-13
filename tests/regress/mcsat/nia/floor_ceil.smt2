(set-logic QF_NIRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (not (= (to_int x) 0)))
(assert (not (= (to_int y) 0)))

(assert (= (to_int (+ x y)) (to_int x)))

(check-sat)

(exit)
