(set-logic LIA)
(set-info :source |Equivalence|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int))
	      (=> (not ((_ divisible 5) x))
		  (or ((_ divisible 5) (+ x 1))
		      ((_ divisible 5) (+ x 2))
		      ((_ divisible 5) (+ x 3))
		      ((_ divisible 5) (+ x 4)))))))

(check-sat)
(exit)
