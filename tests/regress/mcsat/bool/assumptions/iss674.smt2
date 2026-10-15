(set-logic QF_NRA)
(declare-const p Bool)
(check-sat-assuming (p (not p)))
