(set-info :smt-lib-version 2.6)
(set-logic QF_NIA)

(declare-fun x () Int)

(push 1)
(assert (= 0 (div x 5)))
(pop 1)

(assert (and (< x 0) (= 0 (div x 5))))

(check-sat)
