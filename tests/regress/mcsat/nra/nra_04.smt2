(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

;; z = sqrt(2)
(assert (= (* z z) 2))
(assert (> z 0))

;; (x > z) or (y > z)
(assert (or (> x z) (> y z))) 

(check-sat)
(exit)
