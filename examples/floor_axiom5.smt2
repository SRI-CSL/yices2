(set-logic QF_LIRA)
(declare-fun x () Real)
(assert (> (to_int x) x))
(check-sat)
