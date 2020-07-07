(set-logic UF)
(declare-sort mysort 0)

(declare-const a mysort)
(declare-const b mysort)

(define-fun is-power-of-two ((y mysort)) Bool 
  (or (= y a) (= y b)))

(assert
  (forall ((x mysort)) 
  (and (is-power-of-two x) (exists ((y mysort)) (=> (is-power-of-two y) 
							 (and (not (= x a)) (= x y)))
						   )
             )))
(check-sat)
