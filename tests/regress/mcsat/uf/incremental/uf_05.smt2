(set-logic QF_UF)

(declare-fun x1 () Bool)
(declare-fun y1 () Bool)

(declare-fun x2 () Bool)
(declare-fun y2 () Bool)

(push 1)
(assert (or (= x1 y1) (= x2 y2)))
(check-sat)

(declare-fun f (Bool) Bool)

(push 1) 
(assert (distinct (f x1) (f y1)))
(check-sat)

(push 1)
(assert (distinct (f x2) (f y2)))
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(exit)
