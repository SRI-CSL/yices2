(set-logic QF_BV)

(declare-fun y () (_ BitVec 2))

(assert (= #b00 (bvsmod #b00 y)))
(assert (= ((_ extract 1 1) y) #b1))

(check-sat)
