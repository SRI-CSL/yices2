(set-option :produce-unsat-model-interpolants true)
(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (> (+ x y z) 0))
(assert (or (= z 1) (= z 2)))

(check-sat-assuming-model (x y) ((- 1) (- 1)))

(get-unsat-model-interpolant)