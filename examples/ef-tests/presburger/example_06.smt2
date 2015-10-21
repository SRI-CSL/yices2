(set-logic LIA)
(set-info :source |Sum of two odd numbers is even|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x Int) (y Int))
	      (=> (and (not ((_ divisible 2) x)) (not ((_ divisible 2) y)))
		  ((_ divisible 2) (+ x y))))))
(check-sat)
(exit)
