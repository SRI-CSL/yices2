(set-logic ALL)
(declare-fun f () (Array Bool Bool))
(declare-fun g () (Array Bool Bool))

(assert (= f g))
(assert (= (select f false) false))
(assert (= (select g false) false))

(check-sat)
(exit)
