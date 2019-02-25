(set-logic QF_BV)
(declare-fun _substvar_58_ () (_ BitVec 12))
(declare-fun _substvar_62_ () (_ BitVec 6))
(assert (let ((e5 (_ bv24 5))) (let ((e7 (bvashr _substvar_58_ ((_ sign_extend 6) _substvar_62_)))) (let ((e9 (bvadd e7 ((_ sign_extend 7) e5)))) (let ((e12 (ite (= (_ bv1 1) ((_ extract 3 3) _substvar_62_)) (_ bv0 12) _substvar_58_))) (let ((e27 (= e9 (_ bv0 12)))) (let ((e60 (bvsge (_ bv0 12) e12))) (let ((e83 e27)) (let ((e87 e60)) (let ((e101 e87)) (let ((e119 (and e101 e83))) (let ((e120 e119)) e120))))))))))))
(check-sat)

