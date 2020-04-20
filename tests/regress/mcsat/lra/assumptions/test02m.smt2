(set-option :produce-unsat-model-interpolants true)
(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> (+ x y z) 0))

(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))

(get-unsat-model-interpolant)
