(set-option :produce-unsat-model-interpolants true)
(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> (+ x y z) 0))

(push 1)
(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
(get-unsat-model-interpolant) ;; result was unsat, should print
(get-unsat-model-interpolant) ;; no change, should still print
(pop 1)

(get-unsat-model-interpolant) ;; no-checksat, error

(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
(get-unsat-model-interpolant) ;; unsat, should print

(check-sat)
(get-unsat-model-interpolant) ;; sat, error

(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
(get-unsat-model-interpolant) ;; unsat, should print

(push 1)
(get-unsat-model-interpolant) ;; idle, error
(pop 1)

(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
(get-unsat-model-interpolant) ;; unsat, should print

(assert true)
(get-unsat-model-interpolant) ;; not yet, error

(assert false)
(get-unsat-model-interpolant) ;; not yet, error

(check-sat)
(get-unsat-model-interpolant) ;; trivial unsat, should print false
(check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
(get-unsat-model-interpolant) ;; unsat, should still print false

