(set-logic LIA)
(set-info :source |Modulo 3 case analysis fun|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

;; (< x 100) (< y 100) (< 0 x) (< 0 y)

(assert
 (not (forall ((x Int) (y Int))
	      (=> (and (not ((_ divisible 3) x)) (not ((_ divisible 3) y)))
		  (or ((_ divisible 3) (+ x y))
		      ((_ divisible 3) (+ x (* 2 y))))))))
(check-sat)
(exit)
