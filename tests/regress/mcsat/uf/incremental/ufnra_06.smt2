(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-fun h (Real) Real)

(push 1)
(assert (= (* x x) 2))
(check-sat)

(push 1)
(assert (= (* y y) 2))
(check-sat)

(push 1)
(assert (= (* z z) 2))
(check-sat)

;; one pair of x*y y*z z*x must be equal

(push 1)
(assert (not (= (f (* x y)) (f (* y z))))) 
(check-sat)

(push 1)
(assert (not (= (g (* x y)) (g (* z x))))) 
(check-sat)

(push 1)
(assert (not (= (h (* y z)) (h (* z x))))) 
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(pop 1)
(check-sat)

(exit)
