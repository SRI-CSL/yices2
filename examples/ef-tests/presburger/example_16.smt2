(set-logic LIA)
(set-info :source |Simple interval analysis|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x Int))
	      (=> (not ((_ divisible 11) x))
		  (exists ((y Int)) (and (> (* 5 y) 23) ((_ divisible 11) (+ x (+ (* (* 2 3) x) y)))))))))
(check-sat)
(exit)
