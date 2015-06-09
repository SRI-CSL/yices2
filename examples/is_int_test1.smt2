(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (and (< 2 x) (< x 3) (is_int x)))
(check-sat)
