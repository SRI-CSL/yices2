(set-logic UF)
(declare-sort usort 0)

(assert
  (forall ((y usort)) 
  (exists ((x usort)) (= y x))))
(check-sat)
