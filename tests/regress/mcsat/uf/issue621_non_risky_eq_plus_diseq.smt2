(set-logic ALL)
(declare-fun f () (Array Int Bool))
(declare-fun g () (Array Int Bool))

(assert (= f g))
(assert (distinct f g))

(check-sat)
(exit)
