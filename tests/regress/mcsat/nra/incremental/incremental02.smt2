(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)

;; SAT
(push 1)
(assert (= x 0))
(check-sat)
(get-model)

;; UNSAT
(push 1)
(assert (or (< x 0) (> x 0)))
(check-sat)

;; SAT
(pop 1)
(check-sat)
(get-model)

;; SAT
(pop 1)
(check-sat)
(get-model)

(exit)
