(set-logic UF)
(declare-sort usort 0)

(declare-const a usort)
(declare-const b usort)

(assert
  (exists ((x usort)) 	(and	(or (= x a) (= x b)) 
								(forall ((y usort))	(and	(not (= x a))
															(not (= x y)))))))
(check-sat)
