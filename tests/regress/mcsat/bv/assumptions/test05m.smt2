(set-option :produce-unsat-model-interpolants true)

(set-logic QF_BV)

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))

(assert (= x (_ bv0 8)))
(check-sat)

(push 1)

(assert (= y x))
(check-sat)

(push 1)

(assert (= z (bvadd x y)))

(check-sat-assuming-model (z) ((_ bv1 8)))
(get-unsat-model-interpolant)

(pop 1)
(pop 1)
