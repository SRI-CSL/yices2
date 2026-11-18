; Linear problem declared as QF_NIA: solved by the simplex-based solvers, which support divisible; MCSAT does not
(set-logic QF_NIA)
(declare-fun x () Int)
(assert ((_ divisible 3) x))
(assert (> x 4))
(assert (< x 8))
(check-sat)
(get-value (x))
