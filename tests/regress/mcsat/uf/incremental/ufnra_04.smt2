(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)

(push 1)
(assert (= (* x x) 2))
(check-sat)

(push 1)
(assert (= (* y y) 2))
(check-sat)

(push 1)
(assert (= (* z z) 2))
(check-sat)

(push 1)
(assert (not (= (f x) (f y)))) ;; x = -y
(check-sat)

(push 1)
(assert (not (= (f x) (f z)))) ;; x = -z, therefore xy = xz
(check-sat)

(push 1)
(assert (not (= (f (* x y)) (f (* x z)))))
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
