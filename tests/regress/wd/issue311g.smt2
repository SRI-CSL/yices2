(set-logic QF_LRA)
(declare-const r Real)
(assert (= 1.0 (/ r 1 2 3)))
(check-sat)
(get-value (r))


