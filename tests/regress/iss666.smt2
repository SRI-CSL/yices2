(set-logic QF_LRA)
(declare-fun x () Real)
; The let binds a local x. Its scope is only the let body.
; x is not the last binding. The let must still remove it.
; The outer x stays unconstrained, so the result is sat.
(assert (let ((x 0.0) (u 1.0)) (< u 2.0)))
(assert (> x 3.0))
(check-sat)
