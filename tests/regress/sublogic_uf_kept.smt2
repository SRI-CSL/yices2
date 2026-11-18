(set-logic QF_UFLIA)
; Uses an uninterpreted function: the egraph must be kept
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (> (f x) 2))
(assert (< (f x) 4))
(check-sat)
