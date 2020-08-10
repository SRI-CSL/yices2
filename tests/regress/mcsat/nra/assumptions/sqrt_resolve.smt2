(set-option :produce-unsat-model-interpolants true)

(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

;; x^2 = 2
(assert (> x 0))
(assert (= (* x x) 2))
(assert (< (+ x y) 1))
(check-sat-assuming-model (y) (1))
(get-unsat-model-interpolant)
