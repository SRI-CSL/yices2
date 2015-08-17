(set-logic LIA)
(set-info :source |Equivalence|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int))
	      (and (=> (exists ((y Int)) (= (* 6661 y) x))
		       ((_ divisible 6661) x))))))
(check-sat)
(exit)
