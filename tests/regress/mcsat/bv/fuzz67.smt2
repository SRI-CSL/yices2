(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(declare-fun b () Bool)
(assert (not 
  (= 
    #b00 
    (ite b 
      (bvadd 
        (ite (= #b11 x) #b00 (ite (= #b10 x) #b00 y)) 
        y
      ) 
      #b00
    )
  )
))
(check-sat)
(exit)
