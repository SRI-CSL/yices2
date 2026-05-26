(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun p () Bool)
(declare-fun q () Bool)

; p <=> (x = 0x00), q <=> (x > 0x7f)
(assert (= p (= x #x00)))
(assert (= q (bvugt x #x7f)))

; p is satisfiable on its own (x = 0)
(check-sat-assuming (p))

; q is satisfiable on its own (x = 128..255)
(check-sat-assuming (q))

; p AND q require x=0 and x>127 simultaneously -- unsatisfiable
(check-sat-assuming (p q))

; no assumptions: x is unconstrained -- satisfiable
(check-sat)

; push: add a concrete binding that is incompatible with p and q
(push 1)
(assert (= x #x42))
(check-sat)

; p requires x=0 but x=0x42, so assumption p cannot be satisfied
(check-sat-assuming (p))

; q requires x>127 but x=66, so assumption q cannot be satisfied
(check-sat-assuming (q))

(pop 1)

; after pop x is free again: assumption p is satisfiable once more
(check-sat-assuming (p))
