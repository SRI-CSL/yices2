(set-logic UF)
(declare-sort mysort 0)

(declare-const a mysort)
(declare-const b mysort)

(declare-fun myuf (mysort) mysort)

(define-fun is-power-of-two ((y mysort)) Bool 
  (or (not (= y a)) (= y b)))

(assert
  (exists ((x mysort)) 
  (and (is-power-of-two x) (forall ((y mysort)) (=> (is-power-of-two y) 
							 (and (not (= (myuf x) a)) (= x y)))
						   )
             )))
(check-sat)
