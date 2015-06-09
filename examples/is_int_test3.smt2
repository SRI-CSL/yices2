(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (and (< 2 x) (< x 3) (is_int (* 3 x))))
(check-sat)
(get-model)
(get-value (x (* 3 x) (is_int (* 3 x)) (to_int (* 3 x))))

