; Issue 676: rebuilding a one-argument finite-field atom after the
; preprocessor solves x must not mix the rational 0 into field terms.
(set-logic QF_FFA)
(define-sort F () (_ FiniteField 13))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff1 F)))
(assert (= (ff.mul x y) (as ff0 F)))
(check-sat)
(get-value (x y))
