(set-logic QF_BV)
(declare-fun _substvar_28_ () (_ BitVec 12))
(declare-fun _substvar_30_ () (_ BitVec 16))
(assert (let ((e10 (bvnor _substvar_28_ (_ bv0 12)))) (let ((e13 ((_ extract 4 0) _substvar_28_))) (let ((e26 (bvslt _substvar_30_ ((_ sign_extend 11) e13)))) (let ((e34 (bvslt (_ bv0 12) e10))) (let ((e35 (distinct _substvar_30_ (_ bv0 16)))) (let ((e46 (=> e35 e34))) (let ((e52 (ite e26 e46 false))) (let ((e57 e52)) (let ((e59 e57)) (let ((e62 e59)) e62)))))))))))
(check-sat)

