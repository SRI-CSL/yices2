; Issue 676: substituting x = 0 into a finite-field equality must use the
; field zero, not the rational 0.
(set-logic QF_FFA)
(define-sort FF0 () (_ FiniteField 13))
(declare-fun x () FF0)
(declare-fun y () FF0)
(assert (= x (as ff0 FF0)))
(assert (= (ff.mul x y) (as ff1 FF0)))
(check-sat)
