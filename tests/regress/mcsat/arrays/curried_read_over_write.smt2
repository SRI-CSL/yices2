; (RF 0) = (store (RF 1) 0 0) implies (RF 0)[1] = (RF 1)[1]. The equality's
; side (RF 0) is an application returning an array; it was not registered
; as an array term, so the read-over-write check never saw ((RF 0) 1).
(set-logic QF_AUFLIA)
(declare-fun RF (Int) (Array Int Int))
(assert (= (store (RF 1) 0 0) (RF 0)))
(assert (not (= (select (RF 0) 1) (select (RF 1) 1))))
(check-sat)
