(set-logic ALL)
(declare-fun f () (Array Int Bool))
(declare-fun g () (Array Int Bool))

(assert (distinct f g))

(check-sat)
(get-value ((= f g)))
(exit)
