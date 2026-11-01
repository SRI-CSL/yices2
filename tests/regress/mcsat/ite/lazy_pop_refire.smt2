; While the condition c of a registered non-Boolean term t = ite(c, a, b) is
; true on the trail and the trail does not force t to differ from a, when the
; solver calls the ITE plugin to propagate, the ITE plugin shall add a trail
; entry that forces t to equal a.
; c gets its value at level 0. The ITE term registers inside a push, so its
; atom is propagated inside the push and removed by the pop. The ITE term stays
; registered after the pop, and the third check must propagate the atom again.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c () Bool)
(declare-fun p () U)
(declare-fun q () U)
(declare-fun r () U)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(declare-fun f (U) U)
(assert (or c (= p q)))
(assert (= (f p) r))
(assert (not (= (f q) r)))
(check-sat)
(push 1)
(assert (= (f (ite c x y)) z))
(check-sat)
(pop 1)
(assert (= (f (ite c x y)) z))
(assert (not (= (f x) z)))
(check-sat)
