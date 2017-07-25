(set-logic QF_UFNRA)

(declare-sort s 0)
(declare-fun f (s) s)

(declare-fun x0 () s)
(declare-fun x1 () s)
(declare-fun x2 () s)

(check-sat)

(push 1)
(assert (= x0 x1))
(check-sat)

(push 1)
(assert (= x1 x2))
(check-sat)

(push 1)
(assert (not (= (f x0) (f x2))))
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(exit)
