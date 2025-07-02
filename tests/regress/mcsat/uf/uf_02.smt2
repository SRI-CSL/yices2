(set-logic QF_UF)

(declare-sort s 0)

(declare-fun x0 () s)
(declare-fun x1 () s)

(declare-fun y0 () s)

(declare-fun z0 () s)

(assert (or 
   (and (= x0 y0) (= y0 x1))
   (and (= x0 z0) (= z0 x1))
))

(assert (not (= x0 x1)))

(check-sat)
(exit)
