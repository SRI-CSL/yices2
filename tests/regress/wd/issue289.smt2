(set-logic QF_ALIA)
(declare-fun _substvar_44_ () (Array Int Bool))
(declare-const i1 Int)
(declare-const arr0 (Array Int Bool))
(assert (= (store (store arr0 59 true) i1 (not (select (store arr0 59 true) i1))) (store arr0 59 true) _substvar_44_))
(check-sat)
