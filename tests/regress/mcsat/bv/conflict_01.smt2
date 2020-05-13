(set-logic QF_BV)

(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 5))

(assert (or
  (bvsgt x y)
  (bvsgt x z)
))

(assert (=
  (concat x z)
  (concat y x)
))

(check-sat)

(exit)
