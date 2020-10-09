(set-logic UF)
(declare-sort S0 0)
(assert (forall ((x S0) (y S0)) (= x y)))
(check-sat)
