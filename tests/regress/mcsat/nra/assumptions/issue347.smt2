(set-option :produce-models true)
(set-option :produce-unsat-model-interpolants true)

(set-logic QF_NRA)

(declare-fun sv1 () Bool)
(declare-fun sv2 () Bool)
(declare-fun sv3 () Real)
(declare-fun sv4 () Real)
(declare-fun nv1 () Bool)
(declare-fun nv2 () Bool)
(declare-fun nv3 () Real)
(declare-fun nv4 () Real)

(assert (and (and (and (or (= sv2 nv2) sv1) (or sv1 (or sv2 (and (= (+ sv3 (+ (* sv4 (* 2 (* sv3 sv3))) (* (- 2) nv3))) 0) (= (+ sv4 (* (- 2) nv4)) 0))))) (or sv1 (or (not sv2) (and (= sv3 nv3) (= sv4 nv4))))) (or (not sv1) (or (and (= sv4 nv4) (and (= sv3 nv3) (and nv2 (and (not sv2) (<= sv3 (- 2)))))) (and (= sv4 nv4) (and (= sv3 nv3) (and nv2 (and (not sv2) (<= sv4 (- 1))))))))))
(assert (and (not sv2) (not (<= (/ 5208333333333333 125000000000000000) (+ (* sv3 sv3) (* (+ sv4 (- 2)) (+ sv4 (- 2))))))))
(check-sat-assuming-model
  (nv2 nv1 nv4 nv3)
  (false false 1 1)
)
(get-unsat-model-interpolant)
