; Regression test for activation-literal soundness on pop+repush.
; x = 5 and x = 7 bitblast to the same number of unit clauses (8 each,
; one per bit), so cursor-overshoot detection would NOT fire.  Without
; a fresh activation variable the old x=5 clauses leak into the second
; solve and CaDiCaL sees contradictory constraints => wrong UNSAT.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (= x (_ bv5 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv7 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv3 8)))
(check-sat)
(pop 1)
