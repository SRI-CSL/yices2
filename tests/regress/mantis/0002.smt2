(set-logic QF_BV)
(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(declare-fun v1 () (_ BitVec 8))
(declare-fun v2 () (_ BitVec 2))
(assert 
(let ((e8 (bvashr ((_ zero_extend 6) v2) v1)))
(let ((e9 (bvand #b00000001 v1)))
(and (not (= e9 #b00000000)) (not (= e8 #b00000000)))
)))

(check-sat)
