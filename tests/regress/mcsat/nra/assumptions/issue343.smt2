(set-option :produce-unsat-model-interpolants true)

(set-logic QF_NRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (<= (+ (* x x) (* y y)) 2))

(check-sat-assuming-model (x) ((- 2)))
(get-unsat-model-interpolant)