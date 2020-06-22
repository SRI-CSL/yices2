(set-logic LIA)
(declare-const i10 Int)
(assert (exists ((q23 Bool) (q24 Int) (q25 Bool) (q26 Int)) (< (abs i10) q26)))
(check-sat)
