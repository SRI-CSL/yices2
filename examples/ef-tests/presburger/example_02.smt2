(set-logic LIA)
(set-info :source |False example of prime factors|)
(set-info :smt-lib-version 2.0)
(set-info :status sat)

(assert
 (not (forall ((x Int))
	      (=> (and ((_ divisible 3) x) ((_ divisible 5) x))
		  ((_ divisible 13) x)))))
(check-sat)
(get-model)
(exit)
