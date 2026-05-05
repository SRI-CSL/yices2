(set-option :produce-models true)
(set-logic QF_ALIA)

(declare-fun a () (Array Int (Array Int Int)))

(assert (= (select (select a 1) 7) 10))

(check-sat)
(get-model)
(get-value (a))
(get-value ((select a 1)))
(get-value ((select (select a 1) 7)))
