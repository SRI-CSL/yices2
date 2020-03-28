(set-logic QF_UF)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)

(assert (or x y z))

(check-sat-assuming ((not x) (not y) (not z)))
