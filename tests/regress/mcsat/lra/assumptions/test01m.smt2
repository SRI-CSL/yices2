(set-option :produce-unsat-model-interpolants true)
(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (>= (+ x y z) 0))

(check-sat-assuming-model (x y) ((/ 1 2) (/ 1 2)))

(get-model)

(get-unsat-model-interpolant)