(set-logic QF_LRA)
(declare-fun x () Real)
; The let binds a LOCAL x (and u) whose scope is only the let body.
; Since x is not the last binding, it must still be removed from the
; symbol table when the let is closed. The outer x is unconstrained by
; the (tautological) first assertion, so (> x 3.0) is satisfiable.
(assert (let ((x 0.0) (u 1.0)) (< u 2.0)))
(assert (> x 3.0))
(check-sat)
