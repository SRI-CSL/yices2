(set-logic LIA)
(declare-fun i0 () Int)
(assert (forall ((q22 Int)) (or (< q22 (abs i0)) (> q22 (abs i0)))))
(check-sat)
