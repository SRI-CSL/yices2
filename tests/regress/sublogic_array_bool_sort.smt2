; Only 4 arrays from Bool to Bool exist: unsat in an array logic with arithmetic
(set-logic QF_ALIA)
(declare-fun a1 () (Array Bool Bool))
(declare-fun a2 () (Array Bool Bool))
(declare-fun a3 () (Array Bool Bool))
(declare-fun a4 () (Array Bool Bool))
(declare-fun a5 () (Array Bool Bool))
(assert (distinct a1 a2 a3 a4 a5))
(check-sat)
