(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () Bool)
(declare-fun y () Bool)

(assert (= #b11 
  (concat 
    (ite x #b0 #b1) 
    (ite y #b1 #b0)
  )
))

(check-sat)

(exit)

