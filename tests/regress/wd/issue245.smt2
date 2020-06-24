(set-logic LIA)
(declare-const i4 Int)
(assert (forall ((q0 Int) (q1 Bool)) (not (<= q0 i4))))
(check-sat)
