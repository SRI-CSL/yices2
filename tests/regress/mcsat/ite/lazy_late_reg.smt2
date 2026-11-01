; When the solver notifies the ITE plugin of a non-Boolean ITE term whose
; condition already has a value, the ITE plugin shall add the trail entry of
; the selected branch at the next call to propagate.
(set-logic QF_LIA)
(declare-fun c () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(assert c)
(check-sat)
(push 1)
(assert (= (ite c x y) 5))
(assert (= x 3))
(check-sat)
