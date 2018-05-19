(set-logic QF_UFLRA)

(declare-fun f (Real) Real)
(declare-fun p0 (Real) Bool)
(declare-fun p1 (Real) Bool)

(assert (= (ite (p1 0) (- 1) 0) (f 0)))
(assert (= (= 1 (f 0)) (p1 0)))
(assert (= (and (= (f 0) 0) (not (p1 0))) (p0 0)))
(assert (= true (p0 (- 1))))

(push 1)

(assert (not (p0 0)))

(check-sat)

(pop 1)

(assert (not (p0 1)))

(check-sat)

(exit)
