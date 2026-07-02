(set-logic ALL)
(declare-fun f () (Array Int Bool))
(declare-fun g () (Array Int Bool))
(declare-fun h () (Array Int Bool))

(assert (distinct f g h))

(check-sat)
(get-value ((= f g) (= f h) (= g h)))
(exit)
