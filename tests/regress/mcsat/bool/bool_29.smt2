(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UF)
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(assert (let ((e2 
(and
 (or (not v0) (not v1))
 v1
 (or (not v1) v0)
)))
e2
))

(check-sat)
