(set-option :produce-unsat-cores true)
(set-logic QF_UF)

(declare-sort U 0)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun f (U U) U)

(assert (! (= a b) :named a0))
(assert (! (= c d) :named a1))
(assert (! (and p1 true) :named a2))
(assert (! (or (not p1) (and p2 p3)) :named a3))
(assert (! (or (not p3) (not (= (f a c) (f b d)))) :named a4))

(check-sat)

(get-unsat-core)