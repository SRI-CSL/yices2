(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(assert (and (not (= f g)) (not (= g h)) (not (= f h))))
(check-sat)
