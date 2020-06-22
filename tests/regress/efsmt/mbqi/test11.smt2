(set-logic UF)
(declare-sort usort 0)

(declare-const a usort)
(declare-const b usort)

(declare-fun f (usort) usort)


(assert
  (exists ((x usort)) 	(and	(or (= x a) (= x b)) 
								(forall ((y usort))	(not (= (f y) (f x)))))))
(check-sat)
