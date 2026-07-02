(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)

(assert (not (= (select (store a i 10) i) 10)))

(check-sat)
(exit)
