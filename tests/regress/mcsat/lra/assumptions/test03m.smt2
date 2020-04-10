(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

;; sum su to get (x >= 0)
(assert (>= (+ x y z) 0))
(assert (>= (+ x y (- z)) 0))
(assert (>= (+ x (- y) z) 0))
(assert (>= (+ x (- y) (- z)) 0))

(push 1)
(check-sat-assuming-model (x) ((- 1)))
(pop 1)
(check-sat-assuming-model (x) (1))
