; If the condition of a registered non-Boolean ITE term t selects a branch and
; the trail forces t to differ from that branch, then the ITE plugin shall
; report a conflict whose learned clause is (the negated condition literal) or
; (t equals that branch).
; The input atom (= (ite c y z) y) is the plugin's own atom, false when c is set.
(set-logic QF_LRA)
(declare-fun c () Bool)
(declare-fun y () Real)
(declare-fun z () Real)
(assert c)
(assert (not (= (ite c y z) y)))
(check-sat)
