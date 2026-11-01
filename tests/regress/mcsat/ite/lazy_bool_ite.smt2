; When the solver notifies the ITE plugin of a Boolean ITE term, the ITE
; plugin shall add no lemma and no trail entry for that term.
(set-logic QF_LIA)
(declare-fun c () Bool)
(declare-fun x () Int)
(assert (ite c (> x 0) (< x 0)))
(assert (not (> x 0)))
(assert (not (< x 0)))
(check-sat)
