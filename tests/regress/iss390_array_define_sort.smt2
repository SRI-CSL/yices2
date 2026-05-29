; Issue #390: define-sort macros that expand to an Array sort must
; still trigger the SMT-LIB store/const rendering in models.
(set-logic QF_AUFLIA)
(define-sort A () (Array Int Int))
(declare-fun a () A)
(assert (= (select a 0) 1))
(check-sat)
(get-model)
