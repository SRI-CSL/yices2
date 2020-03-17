(set-logic QF_ALIA)
(declare-const arr1 (Array Int Bool))

(declare-const arr2 (Array Int Bool))
(assert (= arr2 (store arr1 10 true)))

(check-sat)
(get-model)
(get-value (arr1 arr2))