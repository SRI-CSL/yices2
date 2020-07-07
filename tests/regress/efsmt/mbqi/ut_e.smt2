(set-logic UF)
(declare-sort mysort 0)

(declare-const a mysort)
(declare-const b mysort)

(define-fun is-power-of-two ((y mysort)) Bool 
  (or (= y a) (= y b)))

(assert
  (= (= a b) (exists ((y mysort)) (=> (is-power-of-two y) 
							 (and (not (= y a)) (= b y)))
						   )
             ))
(check-sat)
