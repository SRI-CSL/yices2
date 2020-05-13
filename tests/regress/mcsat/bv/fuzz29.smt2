(set-logic QF_BV)
(declare-fun _substvar_31_ () (_ BitVec 12))
(declare-fun _substvar_35_ () (_ BitVec 5))
(assert (let ((e17 (bvsub (_ bv0 5) _substvar_35_))) (let ((e40 (= _substvar_35_ (_ bv0 5)))) (let ((e52 (distinct _substvar_31_ (_ bv0 12)))) (let ((e54 (bvslt (_ bv0 5) _substvar_35_))) (let ((e73 (bvsgt ((_ zero_extend 7) e17) _substvar_31_))) (let ((e87 (ite e54 false true))) (let ((e93 (ite e87 false true))) (let ((e115 (not e40))) (let ((e118 e73)) (let ((e120 e115)) (let ((e121 e93)) (let ((e122 (= e52 e120))) (let ((e127 (=> e118 e121))) (let ((e129 (xor e122 e127))) (let ((e132 e129)) (let ((e133 e132)) (let ((e134 e133)) e134))))))))))))))))))
(check-sat)

