; x*x = 1 and x + 1 = 0 force x = 2 mod 3. MCSAT computes x as -1 (the
; symmetric range of Z_3). The model kept -1 unreduced, so x printed as
; #f-1m3 and (= x 2) evaluated to false.
(set-logic QF_FFA)
(define-sort F () (_ FiniteField 3))
(declare-fun x () F)
(assert (= (ff.mul x x) (as ff1 F)))
(assert (= (ff.add x (as ff1 F)) (as ff0 F)))
(check-sat)
(get-value (x (= x (as ff2 F))))
