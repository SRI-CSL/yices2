(set-logic UF)
(declare-sort usort 0)
(declare-sort vsort 0)

(declare-const a usort)
(declare-const b usort)

(declare-fun f (usort) vsort)

(assert
  (exists ((x usort)) 	(and	(or (= x a) (= x b)) 
								(forall ((y usort))	(not (= (f y) (f x)))))))
(check-sat)
