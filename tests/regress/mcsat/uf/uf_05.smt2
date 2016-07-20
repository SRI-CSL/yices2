(set-logic QF_UF)

(declare-fun x1 () Bool)
(declare-fun y1 () Bool)

(declare-fun x2 () Bool)
(declare-fun y2 () Bool)

(declare-fun f (Bool) Bool)

(assert (or (= x1 y1) (= x2 y2)))

(assert (distinct (f x1) (f y1)))
(assert (distinct (f x2) (f y2)))

(check-sat)
(exit)
