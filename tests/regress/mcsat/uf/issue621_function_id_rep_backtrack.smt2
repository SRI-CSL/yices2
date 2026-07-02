(set-logic ALL)
(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))

(push 1)
(assert (= b (store a false true)))
(assert (= (select a false) false))
(check-sat)
(pop 1)

(push 1)
(assert (= b (store a false false)))
(assert (= (select a false) true))
(check-sat)
(pop 1)

(check-sat)
(exit)
