(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)

(push 1)
(assert (= x y))
(check-sat)

(declare-fun f (Real) Real)

(push 1)
(assert (not (= (f (+ x y)) (f y))))
(check-sat)

(pop 1)
(check-sat)

(exit)
