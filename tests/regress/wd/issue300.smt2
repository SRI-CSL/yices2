(set-option :produce-unsat-cores true)
(set-logic QF_ALIRA)
(declare-const r3 Real)
(assert (> 0.0 r3 (/ r3 0.0) 26864806.0))
(check-sat)
(get-unsat-core)

