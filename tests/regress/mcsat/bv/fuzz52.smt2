(set-logic QF_BV)
(declare-fun _substvar_15_ () (_ BitVec 16))
(declare-fun _substvar_17_ () (_ BitVec 12))
(declare-fun _substvar_19_ () (_ BitVec 12))
(assert (let ((e5 (bvudiv _substvar_15_ _substvar_15_))) (let ((e10 (distinct (_ bv0 12) _substvar_19_))) (let ((e15 (bvsgt e5 (_ bv0 16)))) (let ((e20 (= _substvar_15_ (_ bv0 16)))) (let ((e30 (bvsge _substvar_19_ _substvar_17_))) (let ((e37 (= (_ bv0 14) ((_ sign_extend 2) _substvar_17_)))) (let ((e44 (or e10 e30))) (let ((e45 (= e15 e44))) (let ((e57 (not e45))) (let ((e60 (= e57 e37))) (let ((e62 (= e60 false))) (let ((e63 e62)) (let ((e64 (= false e63))) (let ((e66 e64)) (let ((e67 (and e66 (not (= _substvar_15_ (_ bv0 16)))))) e67))))))))))))))))
(check-sat)

