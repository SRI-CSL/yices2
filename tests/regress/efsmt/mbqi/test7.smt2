(set-logic UF)
(declare-sort usort 0)

(declare-fun f (usort) usort)
(declare-const a usort)
(declare-const b usort)

(assert (not (= a b)))
(assert (exists ((y usort)) (forall ((x usort)) (or (= (f x) a) (= (f y) x)))))

(check-sat)
