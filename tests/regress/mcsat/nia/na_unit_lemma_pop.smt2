; Inside the push, x = 6 has no model (194 - 36 is not a sum of two squares),
; and a unit lemma removes 6 from the feasible set of x at base level 1. The
; pop must undo that restriction: x = 6, y = 6 is then a model.
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(push 1)
(assert (= (+ (* x x) (* y y) (* z z)) 194))
(assert (> x 0))
(assert (> y x))
(assert (> z y))
(check-sat)
(pop 1)
(assert (= x 6))
(assert (= y 6))
(check-sat)
(get-value (x y))
