(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 5))

(assert (= #b11 (concat ((_ extract 3 3) x) ((_ extract 3 3) y))))

(check-sat)

(exit)

