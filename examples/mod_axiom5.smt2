(set-logic QF_LIA)
(declare-fun x () Int)
(assert (< (mod x (- 5)) 0))
(check-sat)
