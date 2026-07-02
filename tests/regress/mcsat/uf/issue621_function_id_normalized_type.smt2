(set-logic ALL)
(declare-fun a () (Array Bool Int))
(declare-fun b () (Array Bool Real))

(assert (= a b))
(assert (= (select a false) 0))
(assert (= (select b false) 0.0))

(check-sat)
(exit)
