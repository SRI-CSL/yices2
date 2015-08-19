(set-logic LIA)
(set-info :source |Simple falsity|)
(set-info :smt-lib-version 2.0)
(set-info :status sat)

(assert
 (not (forall ((x Int)) (exists ((y Int))
				(and (> x 0)
				     (not ((_ divisible 5) x))
				     (or ((_ divisible 5) (+ x y 1))
					 ((_ divisible 5) (+ x y 2))
					 ((_ divisible 5) (+ x y 3))
					 ((_ divisible 5) (+ x y 4))))))))

(check-sat)
(get-model)
(exit)
