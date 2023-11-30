(set-logic QF_NIRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun pure_x () Real)
(declare-fun pure_y () Real)
(declare-fun pure_xy () Real)

(assert (= pure_x x))
(assert (< (+ 1 (* (- 1) pure_x)) 0))
(assert (< (+ (- 7) pure_x) 0))

(assert (= pure_y y))
(assert (< (+ 1 (* (- 1) pure_y)) 0))
(assert (< (+ (- 7) pure_y) 0))

(assert (= pure_xy 7))
(assert (= pure_xy (* x y)))

(check-sat)
(exit)
