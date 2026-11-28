; Issue 676: solving x = 0 over a finite field must give x the field zero,
; not the rational 0.
(set-logic QF_FFA)
(define-sort FF0 () (_ FiniteField 13))
(declare-fun x () FF0)
(declare-fun y () FF0)
(assert (= x (as ff0 FF0)))
(assert (= y (ff.add x (as ff3 FF0))))
(check-sat)
(get-value (x y))
