(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 7))
(let ((e3 3))
(let ((e4 (- v1)))
(let ((e5 (* v0 (- e2))))
(let ((e6 (- v0 v1)))
(let ((e7 (* e5 e4)))
(let ((e8 (* v1 e6)))
(let ((e9 (* (- e3) e7)))
(let ((e10 (distinct e7 e4)))
(let ((e11 (distinct e9 e7)))
(let ((e12 (< e4 e9)))
(let ((e13 (< e5 v0)))
(let ((e14 (>= e4 e7)))
(let ((e15 (<= v1 e5)))
(let ((e16 (<= e7 e6)))
(let ((e17 (< e8 e7)))
(let ((e18 (<= e8 e8)))
(let ((e19 (> e7 v0)))
(let ((e20 (= v1 e9)))
(let ((e21 (>= e8 e8)))
(let ((e22 (> e4 e9)))
(let ((e23 (> e9 v1)))
(let ((e24 (> v1 e4)))
(let ((e25 (< e7 v1)))
(let ((e26 (> e4 e5)))
(let ((e27 (>= e7 e5)))
(let ((e28 (= v1 v1)))
(let ((e29 (< v1 e8)))
(let ((e30 (> e7 v1)))
(let ((e31 (<= v1 e5)))
(let ((e32 (distinct e6 e7)))
(let ((e33 
(and
 e10
 e11
 e12
 e13
 e14
 e15
 e16
 e17
 e18
 e19
 e20
 e21
 e22
 e23
 e24
 e25
 e26
 e27
 e28
 e29
 e30
 e31
 e32
)))
e33
)))))))))))))))))))))))))))))))))

(check-sat)
