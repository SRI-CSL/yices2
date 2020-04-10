(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UF)

(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)

(assert (let ((e3 (or v1 v0)))
(let ((e4 (or v2 v2))) ;; true
(let ((e5 (not e4))) ;; false
(let ((e6 (= e3 e5))) ;; (or v1 v0) = false
e6
)))))

(check-sat-assuming-model (v0 v1 v2) (false false false))
