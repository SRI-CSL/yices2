(set-logic QF_BV)
(declare-fun _substvar_97_ () (_ BitVec 10))
(declare-fun _substvar_1017_ () Bool)
(assert (let ((e3 (bvsub (_ bv0 10) _substvar_97_))) (let ((e4 (bvsub _substvar_97_ e3))) (let ((e17 (ite _substvar_1017_ e4 _substvar_97_))) (let ((e25 (bvsgt (_ bv0 10) e17))) (let ((e39 (bvsgt e3 _substvar_97_))) (let ((e68 (not e25))) (let ((e72 (=> e39 false))) (let ((e78 e68)) (let ((e79 e78)) (let ((e85 e72)) (let ((e89 (xor e79 e85))) (let ((e90 e89)) (let ((e91 e90)) (let ((e92 e91)) e92)))))))))))))))
(check-sat)

