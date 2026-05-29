; Issue #390: array-constant marker must be dropped on (pop). After
; popping an Array declaration and re-declaring the same name as a
; unary function, the model must render the function with its
; parameters and not as an array constant.
(set-logic QF_AUFLIA)
(push 1)
(declare-fun a () (Array Int Int))
(assert (= (select a 0) 7))
(check-sat)
(pop 1)
(declare-fun a (Int) Int)
(assert (= (a 0) 5))
(check-sat)
(get-model)
