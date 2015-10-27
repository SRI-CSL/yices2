(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun b () Bool)
(declare-fun x () Bool)
(declare-fun y () Bool)

(assert (ite b x y))
(assert (ite (not b) y x))

(assert (not x))
(assert (not y))

(check-sat)
(exit)
