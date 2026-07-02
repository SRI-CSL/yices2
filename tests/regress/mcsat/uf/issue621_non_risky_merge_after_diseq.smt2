(set-logic ALL)
(declare-fun f () (Array Int Bool))
(declare-fun g () (Array Int Bool))
(declare-fun h () (Array Int Bool))

(assert (distinct f g))
(check-sat)

(push 1)
(assert (= f h))
(assert (= h g))
(check-sat)
(pop 1)

(check-sat)
(exit)
