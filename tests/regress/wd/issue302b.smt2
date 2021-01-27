(set-logic QF_LIRA)
(declare-fun _substvar_100_ () Real)
(declare-fun _substvar_112_ () Real)
(declare-const i5 Int)
(declare-const r1 Real)
(assert (xor true true true (> r1 0.0) true true false true true))
(assert (= (+ 0.0 r1 0.816061 0.0 r1) (to_real i5) r1 _substvar_112_ _substvar_100_))
(check-sat)

