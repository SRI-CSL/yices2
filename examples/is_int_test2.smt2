(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (and (< 2 x) (< x 4) (is_int x)))
(check-sat)
(get-model)
(get-value (x (is_int x) (to_int x)))

