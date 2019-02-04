(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
(declare-fun y () (_ BitVec 1))
(assert 
(let ((e4 (ite (bvult (_ bv0 1) x) (_ bv1 1) (_ bv0 1)))) 
(let ((e7 (bvcomp e4 x))) 
(let ((e10 (bvugt e7 y))) 
(let ((e32 (xor false e10))) 
(let ((e38 e32)) 
(let ((e41 (not e38))) 
(let ((e44 (not e41))) 
(let ((e45 (= e44 false))) e45)))))))))
(check-sat)

