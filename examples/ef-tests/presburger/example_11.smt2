(set-logic LIA)
(set-info :source |Largish example of prime factors with mixed idioms|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int))
	      (and (=> (exists ((y Int)) (= (* 4402921 y) x))
		       (and ((_ divisible 6661) x) ((_ divisible 661) x)))))))
(check-sat)
(exit)
