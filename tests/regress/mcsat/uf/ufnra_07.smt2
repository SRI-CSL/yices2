(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_UFNRA)
(declare-sort x4 0)
(declare-fun x2 () x4)
(declare-fun x1 () x4)
(declare-fun x6 () Real)
(declare-fun x3 (Real) Real)
(declare-fun x5 () Real)
(assert (> (* x5 2.0) x6))
(assert (< x5 x6))
(assert (not (= (x3 (- x6 x5)) 0.0)))
(assert (not (not (= (x3 x6) 0.0))))
(assert (not (= x2 x1)))
(check-sat)
(exit)
