(set-logic LIA)
(set-info :source |Largish example of prime factors|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int))
	      (and (=> (and ((_ divisible 6661) x) ((_ divisible 661) x))  ((_ divisible 4402921) x))
		   (=> ((_ divisible 4402921) x)  (and ((_ divisible 6661) x) ((_ divisible 661) x)))))))
(check-sat)
(exit)
