(set-logic UF)
(declare-fun _substvar_271_ () Bool)
(declare-sort Set 0)
(declare-sort Elem 0)
(declare-fun member (Elem Set) Bool)
(declare-fun subset (Set Set) Bool)
(declare-fun union (Set Set) Set)
(declare-fun intersection (Set Set) Set)
(declare-fun difference (Set Set) Set)
(declare-fun s1 () Set)
(declare-fun s2 () Set)

;(assert (forall ((X Set)) (exists ((E Elem)) (not (member E X)))))
(assert (forall ((X Set) (Y Set)) (=> (forall ((E Elem)) (=> (member E X) (member E Y))) _substvar_271_)))

;(assert (forall ((E Elem) (X Set) (Y Set)) (= (member E (union X Y)) false)))

;(assert (forall ((E Elem) (X Set) (Y Set)) (= (member E (intersection X Y)) false)))

;(assert (forall ((E Elem) (X Set) (Y Set)) (= (member E (difference X Y)) false)))


;(assert (forall ((X Set) (Y Set)) (= false (subset X Y))))
;(assert (subset s2 (union s1 s2)))

(check-sat)
(exit)
