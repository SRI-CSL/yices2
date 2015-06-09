(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (and (< x 0) (>= (to_int x) 0)))
(check-sat)
