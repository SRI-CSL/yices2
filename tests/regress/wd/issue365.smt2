(set-logic UF)
(declare-fun uf4 (Bool Bool Bool Bool) Bool)
(declare-fun v8 () Bool)
(declare-fun v9 () Bool)
(assert (uf4 true false true false))
(assert (forall ((q23 Bool)) (or (xor v9 q23 q23 v8 q23) (exists ((q9 Bool)) q9))))
(check-sat)
