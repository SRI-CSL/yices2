(set-option :produce-assignments true)
(set-logic QF_UFLIA)
(declare-fun I () Int)
(declare-fun B0 () Bool)
(declare-fun B1 () Bool)
(assert (and
 (=> (= I 3) (= B0 true))
 (=> (not (distinct I 1 3)) (= B1 false))
 (=> (not (distinct I 1 2)) (= B1 false))
 (=> (not (distinct I 0 2)) (= B1 false))
 ))
(check-sat)
(exit)

