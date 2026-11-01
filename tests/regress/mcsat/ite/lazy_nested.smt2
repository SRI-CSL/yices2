; While the condition c of a registered non-Boolean term t = ite(c, a, b) is
; true on the trail and the trail does not force t to differ from a, when the
; solver calls the ITE plugin to propagate, the ITE plugin shall add a trail
; entry that forces t to equal a.
; While the condition c of a registered non-Boolean term t = ite(c, a, b) is
; false on the trail and the trail does not force t to differ from b, when the
; solver calls the ITE plugin to propagate, the ITE plugin shall add a trail
; entry that forces t to equal b.
(set-logic QF_LIA)
(declare-fun c1 () Bool)
(declare-fun c2 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert c1)
(assert (not c2))
(assert (not (= (ite c1 (ite c2 x y) z) y)))
(check-sat)
