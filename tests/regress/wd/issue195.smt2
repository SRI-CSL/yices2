(set-logic LIA)
(declare-const i12 Int)
(assert (forall ((q8 Bool) (q9 Int) (q10 Int)) (>= q10 i12)))
(check-sat)
