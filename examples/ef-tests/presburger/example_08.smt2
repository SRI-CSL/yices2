(set-logic LIA)
(set-info :source |Simple interval analysis|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x0 Int) (x1 Int) (x2 Int))
	      (=> (and (not ((_ divisible 11) x0)) (not ((_ divisible 11) x1)))
		  (exists ((y Int))
			  (and (< x2 y)
			       (<= y (+ x2 11))
			       ((_ divisible 11) (+ x0 (+ x1 y)))))))))
(check-sat)
(exit)
