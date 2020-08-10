(set-option :produce-unsat-model-interpolants true)
(set-logic QF_UF)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)

(assert (or x y z))
(assert (or x y (not z)))
(assert (or x (not y) z))
(assert (or x (not y) (not z)))

(push 1)
(check-sat-assuming-model (x) (false))
(get-unsat-model-interpolant)
(pop 1)
(check-sat-assuming-model (x) (true))
