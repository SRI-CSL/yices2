(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
(assert 
  (let ((e9 (concat x (_ bv0 1)))) 
  (let ((e13 ((_ rotate_left 0) e9))) 
  (let ((e15 (bvadd e13 e13))) 
  (let ((e24 (bvneg e15))) 
  (let ((e535 (not (= e24 (_ bv0 2))))) 
    e535
))))))
(check-sat)

