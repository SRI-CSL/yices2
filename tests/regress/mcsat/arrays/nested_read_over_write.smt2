; Same as curried_read_over_write.smt2 with nested arrays: (select M 0) is
; an application returning an array.
(set-logic QF_ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(assert (= (store (select M 1) 0 0) (select M 0)))
(assert (not (= (select (select M 0) 1) (select (select M 1) 1))))
(check-sat)
