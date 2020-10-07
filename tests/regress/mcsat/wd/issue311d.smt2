(set-logic QF_NRA)
(declare-const r Real)
(assert (not (= r 0)))
(assert (= 1.0 (/ 2 3 4 5 r)))
(check-sat)
(get-value (r))


