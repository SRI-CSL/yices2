(set-option :produce-unsat-model-interpolants true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 7))
(declare-fun y () (_ BitVec 7))
(assert
  (=
   #b0111001
   (bvadd (bvmul #b1010011 x) (bvmul #b1111000 y))
  )
)

(assert
 (or
   (= (bvmul #b0111101 x) #b1101110)
   (bvsge (bvmul #b1011011 x) #b0111010)
   (not (=
     #b0111001
    (bvadd #b1010000 (bvmul #b1010011 x))
   ))
 )
)

(check-sat-assuming-model
 (y x)
 (#b0000110 #b0000000)
)

(get-unsat-model-interpolant)
