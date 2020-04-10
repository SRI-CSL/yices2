(set-logic QF_UF)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)

(assert (or x y z))

(check-sat-assuming-model (x y) (false false))

(get-model)