(set-logic QF_BV)

(declare-fun x () (_ BitVec 1))
(declare-fun y () (_ BitVec 1))
(declare-fun b () Bool)

(assert
  (let ((e5 (bvsdiv x y)))
  (let ((e7 (bvsrem x x)))
  (let ((e18 (_ bv1 1)))
  (let ((e20 (bvudiv (_ bv0 1) e7)))
  (let ((e37 (ite
    (bvsgt e20 e18)
    (_ bv1 1)
    (_ bv0 1))))
  (let ((e44 (bvcomp (_ bv0 1) e5)))
  (let ((e175 (bvslt e37 e44)))
  (let ((e309 (xor e175 true)))
  (let ((e315 (and e309 (not (= e5 (_ bv0 1))))))
  (let ((e319 (and e315 b)))

    e319
)))))))))))
(check-sat)