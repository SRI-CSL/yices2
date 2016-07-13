(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real Real Real) Real)

(assert (= 0 (* (- x 1) (- x 2) (- x 3)))) ;; x = 1, 2, 3
(assert (= 0 (* (- y 1) (- y 2) (- y 3)))) ;; y = 1, 2, 3
(assert (= 0 (* (- z 1) (- z 2) (- z 3)))) ;; z = 1, 2, 3

(assert (= (* x y z) 6)) ;; x y z distinct 1 2 3

(assert (not (= (f x y z) (f 1 2 3)))) 
(assert (not (= (f x y z) (f 1 3 2)))) 
(assert (not (= (f x y z) (f 2 1 3)))) 
(assert (not (= (f x y z) (f 2 3 1)))) 
(assert (not (= (f x y z) (f 3 1 2)))) 
(assert (not (= (f x y z) (f 3 2 1)))) 

(check-sat)
(exit)
