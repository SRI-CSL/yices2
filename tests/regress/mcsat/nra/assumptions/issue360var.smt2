(set-option :produce-unsat-model-interpolants true)

(set-logic QF_NRA)

(declare-const x14 Real)
(declare-const x23 Real)
(declare-const x10 Real)

(assert
  (and (>= (* (- 1.0) x10) 0.0)
       (>= (+ (* x14 x14) (* x14 x14 x23) x10) 0.0)
       (not (= (+ (* x14 x14) x10) 0))
       (>= (+ (* (- 1.0) x14) (* x10 x10)) 0.0)))

(check-sat-assuming-model (x23 x14) (0 1))
(get-unsat-model-interpolant)


  