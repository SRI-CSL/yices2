(set-logic LIA)
(set-info :source |Either x or x + 1 is even, gussied up to look like a tart|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x Int))
	      (=> ((_ divisible 2) x)
		  (forall ((y Int)) (or ((_ divisible 2) (+ x y)) ((_ divisible 2) (+ x  (+ y 1)))))))))
(check-sat)
(exit)
