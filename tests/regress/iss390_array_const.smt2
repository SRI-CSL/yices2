; Issue #390: declare-const path for SMT-LIB arrays must also render as
; a 0-arity Array constant in (get-model).
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const b Int)
(assert (= (select a 0) 1))
(assert (= b 99))
(check-sat)
(get-model)
