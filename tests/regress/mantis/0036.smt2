(set-option :produce-models true)
(set-logic QF_AUFLIA)

(declare-fun S0 () (Array Int Int))
(declare-fun S1 () (Array Int Int))
(declare-fun z () Int)

(assert (>= z 0))
(assert (< z 4))

(assert  (and (= (select S0 0) 0) (and (= (select S0 1) 1) (and (= (select S0 2) 2) (= (select S0 3) 3)))))

(assert (= S1 (store S0 1 1)))
(assert (= z (select S1 2)))

(check-sat)
(get-value (z))
; it should be 2
(exit)
