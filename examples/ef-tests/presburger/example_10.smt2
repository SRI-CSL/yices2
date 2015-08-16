(set-logic LIA)
(set-info :source |Modulo 5 case analysis fun|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)


(assert
 (not (forall ((x Int) (y Int) (w Int))
	      (=> (and (not ((_ divisible 5) x)) (not ((_ divisible 5) y)))
		  (or
		   ((_ divisible 5) (+ x y)) 
		   ((_ divisible 5) (+ x (* 2 y)))
		   ((_ divisible 5) (+ (* 2 x) y)) 
		   ((_ divisible 5) (+ (* 2 x) (* 3 y)))
		   ((_ divisible 5) (+ (* 3 x) (* 2 y)))
		   )))))

(check-sat)
(exit)
