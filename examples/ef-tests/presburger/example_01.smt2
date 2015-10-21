(set-logic LIA)
(set-info :source |Simple example of prime factors|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int))
	      (and (=> (and ((_ divisible 3) x) ((_ divisible 5) x))  ((_ divisible 15) x))
		   (=> ((_ divisible 15) x) (and ((_ divisible 3) x) ((_ divisible 5) x)))))))
(check-sat)
(exit)
