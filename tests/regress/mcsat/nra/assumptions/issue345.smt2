(set-option :produce-unsat-model-interpolants true)
(set-logic QF_NRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (not (<= (/ 1 4) (+ (* (+ x (- 1)) (+ x (- 1))) (* (+ 1 y) (+ 1 y))))))

;; 1/4 > (x - 1)^2 + (y + 1)^2
;; interval inference
;; - x: (1/2, 3/2)
;; - y: (-3/2, -1/2)
;;
;; should learn: (x - 1)^2 < 1/4, i.e. 4x^2 - 8x + 3 < 0
;;
;; constraint evaluates to false: OK
;;

;; model to refute:
;; (= b false)
;; (= y -17/32)
;; (= x 23/16)
(check-sat-assuming-model (y x) ((/ (- 17) 32) (/ 23 16)))
(get-unsat-model-interpolant)

;; wrong model interpolant:
;; (arith-ge 3 - 8*x + 4*x^2 0)
(push 1)
(assert (not
  (>= (+ 3 (* (- 8) x) (* 4 (* x x))) 0)
))
(check-sat)
(pop 1)

(push 1)
(assert (not
  (< (+ (/ 7 4) (* (- 2) x) (* 2 y) (* x x) (* y y)) 0)
))
(check-sat)
(pop 1)