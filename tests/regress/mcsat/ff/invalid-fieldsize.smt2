(set-info :smt-lib-version 2.6)
(set-logic QF_FFA)
; 6 is not prime
(define-sort FF0 () (_ FiniteField 6))
(declare-fun x0 () FF0)
(declare-fun x1 () FF0)

(assert (= (ff.add x0 x1) (as ff0 FF0)))
