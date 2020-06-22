(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert
 (=
  (bvadd
   (bvmul (concat (_ bv64 5) x) (concat (_ bv64 5) x))
   (concat (_ bv64 5) x)
   (bvmul (concat (_ bv64 5) x) (concat (_ bv64 5) x)))
  
  (bvadd
   (concat (_ bv64 5) x)
   (bvmul (concat (_ bv64 5) x) (concat (_ bv64 5) x)))

  (concat (_ bv64 5) x)))

(check-sat)

