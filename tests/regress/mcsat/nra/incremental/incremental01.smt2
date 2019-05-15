(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)

;; SAT
(push 1) 
(assert (<= (+ (* x x) (* y y)) 1))
(check-sat)

;; UNSAT
(push 1)
(assert (> (* x y) 1))
(check-sat)

;; SAT
(pop 1)
(check-sat)

;; SAT
(pop 1)
(check-sat)

(exit)
