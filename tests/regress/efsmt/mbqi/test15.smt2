(set-logic UF)
(declare-sort usort 0)

(declare-const a usort)
(declare-const b usort)
(declare-const c usort)

(declare-fun P (usort) Bool)
(declare-fun R (usort) Bool)
(declare-fun S (usort) Bool)

(assert (not (P a)))
(assert (R b))
(assert (S c))

(assert (forall ((x usort)) (or (R x) (S x))))
(assert (forall ((x usort)) (or (not (R x)) (P x))))
(assert (forall ((x usort)) (or (not (S x)) (P x))))

(check-sat)
