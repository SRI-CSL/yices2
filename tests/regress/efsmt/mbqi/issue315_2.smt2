(set-logic UF)
(declare-sort S0 0)
(assert (not (exists ((q3 S0) (q4 S0) (q5 Bool) (q6 Bool) (q7 S0) (q8 Bool)) (=> (= q3 q4 q7) false))))
(check-sat)
