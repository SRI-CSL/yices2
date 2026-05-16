; Tests level-0 cursor handling across multiple solves.
; Generates long clauses at level 0 via complex comparisons, then
; interleaves level-0 and level-1 check-sats to exercise the
; fwd_clauses[0] cursor across potential simplify_clause_database calls.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
(assert (bvult x #x8000))
(assert (bvult y #x8000))
(assert (bvult x y))
(check-sat)
(push 1)
(assert (= x #x0001))
(check-sat)
(pop 1)
(assert (bvugt x #x0000))
(check-sat)
(push 1)
(assert (= y #x7fff))
(check-sat)
(pop 1)
(check-sat)
