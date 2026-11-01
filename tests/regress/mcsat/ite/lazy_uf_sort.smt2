; If the condition of a registered non-Boolean ITE term t selects a branch and
; the trail forces t to differ from that branch, then the ITE plugin shall
; report a conflict whose learned clause is (the negated condition literal) or
; (t equals that branch).
; The input atom (= (ite c u v) u) is the plugin's own atom, false when c is set.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c () Bool)
(declare-fun u () U)
(declare-fun v () U)
(assert c)
(assert (not (= (ite c u v) u)))
(check-sat)
