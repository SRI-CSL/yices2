(set-logic QF_BV)
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 2))
(declare-fun x3 () (_ BitVec 3))
(declare-fun x4 () (_ BitVec 3))

(assert 
  (let ((?v_2 ((_ extract 2 0) x1))) 
  (let ( (?v_8 ((_ extract 1 1) x1))) 
  (let ( (?v_12 (= ?v_8 (_ bv1 1)))) 
  (let ( (?v_17 ((_ extract 2 2) x1))) 
  (let ( (?v_21 (= ?v_17 (_ bv1 1)))) 
  (not 
    (=> 
      (and (= ((_ extract 1 0) x0) (_ bv3 2)) (= x2 (_ bv3 2))) 
      (=> 
        (and 
          (and 
            (and 
              (ite (= ((_ extract 0 0) x0) (_ bv1 1)) (= x3 x4) (= x3 (_ bv0 3))) 
              (ite (= ((_ extract 1 1) x0) (_ bv1 1)) (= ?v_2 (concat x2 (_ bv0 1))) (= ?v_2 (_ bv0 3)))
            ) 
            (= (_ bv0 1) (ite ?v_12 (_ bv1 1) (_ bv0 1)))
          ) 
          (= (_ bv0 1) (ite ?v_21 (_ bv1 1) (_ bv0 1)))
        ) 
        false
      )
    )
  )
))))))

(check-sat)
(exit)
