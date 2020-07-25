(set-option :produce-unsat-model-interpolants true)

(set-logic QF_NRA)

(declare-const x Real)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

;; x^2 < y
(assert (= (+ (* a x x) (* b x) c) 0))
(check-sat-assuming-model (a b c) (1 1 1))
(get-unsat-model-interpolant)
