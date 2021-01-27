(set-logic QF_UF)
(declare-fun P (Bool Bool) Bool)
(assert (P true false))
(check-sat)
