(set-logic QF_UFNRA)
(declare-sort s 0)
(declare-fun x () s)
(declare-fun y () s)
(declare-fun z () s)

(check-sat)

(push 1)
(assert (= x y))
(check-sat)

(push 1)
(assert (= y z))
(check-sat)

(push 1)
(assert (not (= x z)))
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(exit)
