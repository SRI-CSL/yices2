(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> (mod x (- 5)) 4))
(check-sat)
