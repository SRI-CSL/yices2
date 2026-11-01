; While the condition c of a registered non-Boolean term t = ite(c, a, b) has
; no value on the trail, when the atom (t = a) becomes false on the trail, the
; ITE plugin shall add a trail entry that sets c to false with the literal
; (not (t = a)) as the only reason.
; NA assigns t at base level from its two bounds, before c has a value.
(set-option :produce-models true)
(set-logic QF_NIA)
(declare-fun c () Bool)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= (ite c y z) 2))
(assert (<= (ite c y z) 2))
(assert (= (* y y) 1))
(assert (> y 0))
(assert (= (* z z) 4))
(assert (> z 0))
(check-sat)
(get-value (c))
