(set-logic UF)
(declare-sort mysort 0)

(declare-const a mysort)
(declare-const b mysort)

(declare-fun F (mysort) mysort)

(assert (not (= a b)))

(assert
  (forall ((y mysort)) 
  (and (or (= y a) (= y b)) (exists ((x mysort)) (or (not (= (F x) a))
													 (and (not (= (F x) y)) true))
						   )
             )))
(check-sat)
