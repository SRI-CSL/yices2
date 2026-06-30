(set-logic ALL)
(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))

(assert (= b (store a false true)))
(assert (= (select a false) false))
(assert (= (select b false) true))

(check-sat)
(exit)
