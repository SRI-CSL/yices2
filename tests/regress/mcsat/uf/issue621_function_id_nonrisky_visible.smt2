(set-logic ALL)
(declare-fun f () (Array Int Bool))
(declare-fun g () (Array Int Bool))

(assert (= f g))
(assert (= (select f 0) true))
(assert (= (select g 0) true))

(check-sat)
(exit)
