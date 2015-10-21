(set-logic LIA)
(set-info :source |Fact about divisiblity|)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(assert
 (not (forall ((x Int) (y Int) )
	      (=> (not ((_ divisible 7) (+ x y)))
		  (forall ((z Int)) (not ((_ divisible 7) (+ (+ x (* 7 z)) y))))))))
(check-sat)
(exit)
