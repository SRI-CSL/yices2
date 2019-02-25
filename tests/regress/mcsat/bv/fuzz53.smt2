(set-logic QF_BV)
(declare-fun _substvar_14_ () (_ BitVec 15))
(declare-fun _substvar_16_ () (_ BitVec 15))
(assert (let ((e8 (ite (bvsgt _substvar_16_ _substvar_14_) (_ bv1 1) (_ bv0 1)))) (let ((e12 (bvurem e8 e8))) (let ((e152 (not (= e8 (_ bv0 1))))) (let ((e153 (and e152 (not (= e12 (_ bv0 1)))))) e153)))))
(check-sat)

