(set-option :produce-unsat-model-interpolants true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(declare-fun z () (_ BitVec 2))
(declare-fun a () Bool)
(assert
 (or
  (not
   (or
    (not
      (=
       #b01
       x))
    (not
      (=
       #b00
       y))
    (not
     (=
      (ite
       (bvuge
        x
        #b00)
       x
       (bvadd x y))
      z))))
  (not a)))
(check-sat-assuming-model
 (a z y x)
 (true
  #b00
  #b00
  #b00))
(get-unsat-model-interpolant)