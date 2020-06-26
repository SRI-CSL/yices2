(set-logic QF_ALIA)

(declare-fun x283 () Bool)
(declare-fun x538 () Int)
(declare-fun x548 () Int)
(declare-const i4 Int)
(declare-const i10 Int)
(declare-const v18 Bool)
(declare-const arr (Array Bool Int))

(assert (or (= x548 i10 0) (= (- i4 77) i10)))

(assert (or x283 (< (select (store arr v18 80) false) i4)))

(check-sat)
