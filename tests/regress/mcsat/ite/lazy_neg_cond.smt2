; While the condition c of a registered non-Boolean term t = ite(c, a, b) is
; false on the trail and the trail does not force t to differ from b, when the
; solver calls the ITE plugin to propagate, the ITE plugin shall add a trail
; entry that forces t to equal b.
(set-logic QF_LIA)
(declare-fun c () Bool)
(declare-fun p () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (=> p (not c)))
(assert p)
(assert (= (ite c x y) 3))
(assert (= y 4))
(check-sat)
