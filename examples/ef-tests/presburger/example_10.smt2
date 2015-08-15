(set-logic LIA)
(set-info :source |Modulo 5 case analysis fun|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x Int) (y Int) (w Int))
	      (=> (and (not ((_ divisible 11) x)) (not ((_ divisible 11) y)))
		  (exists ((z Int))
			  (and (< w z)
			       (<= z (+ w 11))
			       ((_ divisible 11) (+ x y z))))))))
(check-sat)
(exit)
