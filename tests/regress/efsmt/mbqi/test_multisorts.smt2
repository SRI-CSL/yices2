(set-logic UF)
(declare-sort sortA 0)
(declare-sort sortB 0)

(declare-fun f (sortB) sortA)

(assert
	(exists ((x sortA) (y sortA))
		(and
			(not (= x y))
			(forall ((z sortB)) (= (f z) y))
)))

(check-sat)
