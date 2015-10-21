(set-logic LIA)
(set-info :source |Modulo 4 case analysis fun|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int) (y Int) (w Int))
	      (=> (and (not ((_ divisible 4) x)) (not ((_ divisible 4) y)))
		  (or ((_ divisible 4) (+ (* 2 x) (* 2 y)))
		      ((_ divisible 4) (+ (* 2 x) y)) 
		      ((_ divisible 4) (+ x y)) 
		      ((_ divisible 4) (+ x (* 2 y))))))))
(check-sat)
(exit)
