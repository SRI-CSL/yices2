(set-logic LIA)
(declare-const i6 Int)
(assert (exists ((q17 Bool) (q18 Int) (q19 Int)) (distinct (abs (mod i6 36)) 0)))
(check-sat)
