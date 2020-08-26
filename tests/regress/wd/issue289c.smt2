(set-logic QF_ALIA)
(declare-const arr0 (Array Int Bool))
(assert (= (store arr0 59 (not (select arr0  59))) arr0))
(check-sat)
