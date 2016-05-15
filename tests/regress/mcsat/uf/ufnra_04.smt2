(set-logic QF_UFNRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)

(assert (= (* x x) 2))
(assert (= (* y y) 2))
(assert (= (* z z) 2))
(assert (not (= (f x) (f y)))) ;; x = -y
(assert (not (= (f x) (f z)))) ;; x = -z, therefore xy = xz
(assert (not (= (f (* x y)) (f (* x z)))))

(check-sat)
(exit)
