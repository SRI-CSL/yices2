(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)

;; SAT
(assert (> x 0))
(assert (> y 0))
(assert (= (* x x) 2))
(check-sat)
(get-model)

;; SAT
(push 1)
(assert (= (* y y) 3))
(check-sat)
(get-model)

;; UNSAT
(push 1)
(assert (= x y)) 
(check-sat)

;; SAT
(pop 1)
(check-sat)
(get-model)

;; SAT
(pop 1) 
(check-sat)
(get-model)

(exit)
