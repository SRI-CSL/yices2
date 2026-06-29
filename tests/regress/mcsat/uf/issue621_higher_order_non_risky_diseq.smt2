(set-logic ALL)
(declare-fun f () (Array (Array Int Bool) Bool))
(declare-fun g () (Array (Array Int Bool) Bool))

(assert (distinct f g))

(check-sat)
(get-value ((= f g)))
(exit)
