; When the solver asks the ITE plugin to explain a trail entry that forces t to
; equal a, the ITE plugin shall return the literal c as the only reason.
; While the condition c of a registered non-Boolean term t = ite(c, a, b) has
; no value on the trail, when the atom (t = a) becomes false on the trail, the
; ITE plugin shall add a trail entry that sets c to false with the literal
; (not (t = a)) as the only reason.
; Conflict analysis resolves one atom and one condition that the ITE plugin
; propagated. The propagation check validates each explanation in debug builds.
(set-logic QF_LIA)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun t () Int)
(assert (= (ite c x y) t))
(assert (= (ite (not d) y x) t))
(assert (> t 3))
(assert (= y 4))
(assert (= x 5))
(assert (or (not c) (not d)))
(assert (or c d))
(assert (not (= t 4)))
(check-sat)
