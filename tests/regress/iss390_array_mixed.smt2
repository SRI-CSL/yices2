; Issue #390: regression guard. An Array-declared constant must use
; store/const form while a real unary function declared in the same
; problem must keep the (define-fun f ((x!0 K)) V (ite ...)) form.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(assert (= (select a 0) 1))
(assert (= (select a 1) 3))
(assert (= (f 0) 5))
(assert (= (f 1) 7))
(check-sat)
(get-model)
