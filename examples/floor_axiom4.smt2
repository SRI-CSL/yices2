(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (>= (to_int x) (+ x 1)))
(check-sat)
