(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

;; x = y + z
(assert (= x (+ y z)))

;; z = sqrt(2)
(assert (= (* z z) 2))
(assert (> z 0))

;; y = sqrt(3)
(assert (= (* y y) 3))
(assert (> y 0))

(check-sat)
(exit)
