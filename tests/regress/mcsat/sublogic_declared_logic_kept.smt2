; Error text must refer to the declared logic QF_NIA, not the sublogic used for the check
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (> x 2))
(assert (< x 2))
(check-sat)
(get-unsat-model-interpolant)
