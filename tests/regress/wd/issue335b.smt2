(set-logic QF_ALIA)
(declare-fun x () Bool)
(declare-fun arr0 () (Array Bool Int))

(define-const b (Array Bool Int) (store arr0 false 39))

(assert (or (>= (select (store b (= arr0 b) 1127) false) 65) x))
(assert (distinct (store b (= arr0 b) 1127) b arr0))

(check-sat)
;;(get-model)
