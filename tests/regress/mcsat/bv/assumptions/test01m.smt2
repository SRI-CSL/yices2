(set-logic QF_BV)

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))

(assert (bvslt (bvadd x y z) (_ bv0 8)))

(check-sat-assuming-model (x y) ((_ bv0 8) (_ bv0 8)))

(get-model)