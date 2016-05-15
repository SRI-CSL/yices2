(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-fun h (Real) Real)

(assert (= (* x x) 2))
(assert (= (* y y) 2))
(assert (= (* z z) 2))

;; one pair of x*y y*z z*x must be equal

(assert (not (= (f (* x y)) (f (* y z))))) 
(assert (not (= (g (* x y)) (g (* z x))))) 
(assert (not (= (h (* y z)) (h (* z x))))) 

(check-sat)
(exit)
