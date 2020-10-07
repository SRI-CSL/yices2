(set-logic QF_NRA)
(declare-const r Real)
(assert (not (= r 0)))
(assert (= 1.0 (/ (- 1) r r r)))
(check-sat)
(get-value (r))


