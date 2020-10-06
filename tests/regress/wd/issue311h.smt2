(set-logic QF_NRA)
(declare-const r Real)
(assert (not (= r 0)))
(assert (= 1.0 (/ 1.0 r (= r 10))))
(check-sat)
(get-value (r))

