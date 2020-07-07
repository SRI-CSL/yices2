(set-logic UF)
(declare-sort usort 0)

(declare-fun f (usort) usort)
(declare-const a usort)
(declare-const b usort)

(assert (not (= a b)))
(assert (forall ((x usort)) (= (f b) x)))

(check-sat)
