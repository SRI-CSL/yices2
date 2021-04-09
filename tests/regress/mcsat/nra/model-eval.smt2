(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (= (* x x) 2))
(assert (= (* y y) 3))
(assert (= (* z z) 5))

(check-sat)

(get-value (x y z))
(get-value ((+ x y z) (+ x y z 1) (+ (* 2 x) (* 3 y) (* 5 z) 1)))
(get-value ((* 2 x y z) (/ (/ x y) (/ z 2)) (* (* x y) (/ x y))))
(get-value ((= (* x x y y z z) (* 2 3 5))))
(get-value ((< (* x x y y z z) (* 2 3 5))))
(get-value ((<= (* x x y y z z) (* 2 3 5))))