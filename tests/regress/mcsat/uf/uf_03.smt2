(set-logic QF_UF)

(declare-sort s 0)
(declare-fun f (s) s)

(declare-fun x0 () s)
(declare-fun x1 () s)
(declare-fun x2 () s)

(assert (= x0 x1))
(assert (= x1 x2))

(assert (not (= (f x0) (f x2))))

(check-sat)
(exit)
