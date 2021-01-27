(set-logic QF_NIA)
(declare-fun i2 () Int)
(assert (= true true true true (distinct 0 (abs i2) 3337)))
(check-sat)
