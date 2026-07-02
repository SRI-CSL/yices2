(set-logic ALL)
(declare-fun f () (Array Bool Bool))
(declare-fun g () (Array Bool Bool))
(declare-fun h () (Array Bool Bool))

(assert (= f g))
(assert (= h (store g false true)))
(assert (= (select g false) false))
(assert (= (select h false) true))

(check-sat)
(exit)
