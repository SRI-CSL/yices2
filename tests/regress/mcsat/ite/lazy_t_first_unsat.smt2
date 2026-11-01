; If the condition of a registered non-Boolean ITE term t selects a branch and
; the trail forces t to differ from that branch, then the ITE plugin shall
; report a conflict whose learned clause is (the negated condition literal) or
; (t equals that branch).
; NA assigns t at base level from its two bounds, before c has a value.
(set-logic QF_NIA)
(declare-fun c () Bool)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= (ite c y z) 5))
(assert (<= (ite c y z) 5))
(assert (= (* y y) 1))
(assert (> y 0))
(assert (= (* z z) 4))
(assert (> z 0))
(check-sat)
