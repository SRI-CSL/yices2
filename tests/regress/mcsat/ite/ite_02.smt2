(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)

(assert (<= (* x x) 1))
(assert (<= (* y y) 1))

(assert 
  (>= 
    (+ (ite b1 x y) (ite b2 x y))
    2
  )
)

(check-sat)
(exit)
