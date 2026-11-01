; While the condition c of a registered non-Boolean term t = ite(c, a, b) is
; true on the trail and the trail does not force t to differ from a, when the
; solver calls the ITE plugin to propagate, the ITE plugin shall add a trail
; entry that forces t to equal a.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c () Bool)
(declare-fun u () U)
(declare-fun v () U)
(assert c)
(assert (not (= (ite c u v) u)))
(check-sat)
