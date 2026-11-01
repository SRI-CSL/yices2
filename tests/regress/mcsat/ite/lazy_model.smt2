; When the solver returns sat, the solver shall return a model in which the
; value of each non-Boolean ITE term equals the value of the selected branch
; of that term.
(set-option :produce-models true)
(set-logic QF_LRA)
(declare-fun c () Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 7))
(assert (= y 1))
(assert (> (ite c x y) 5))
(check-sat)
(get-value ((ite c x y) c))
