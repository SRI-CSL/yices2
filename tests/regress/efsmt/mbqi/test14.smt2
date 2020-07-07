(set-logic UF)

(declare-sort usort 0)
(declare-fun f (usort) usort)
(declare-fun g (usort) usort)
(declare-const a usort)
(declare-const b usort)

(assert (not (= a b)))
(assert (= (f a) b))
(assert (not (= (g b) a)))
(assert (forall ((x usort)) (= (f x) (g x))))

(check-sat)
