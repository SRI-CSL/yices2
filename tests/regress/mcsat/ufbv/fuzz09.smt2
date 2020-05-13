(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 16))
(declare-fun p1 ((_ BitVec 27) (_ BitVec 22)) Bool)
(assert 
  (let ((e6 (ite (p1 (_ bv0 27) ((_ zero_extend 6) x)) (_ bv1 1) (_ bv0 1)))) 
  (let ((e7 (p1 (_ bv0 27) ((_ zero_extend 21) e6)))) 
  (let ((e13 (distinct (_ bv0 16) x))) 
  (let ((e19 e7)) 
  (let ((e22 (= false e13))) 
  (let ((e27 e22)) 
  (let ((e28 (and e27 e19))) e28))))))))
(check-sat)

