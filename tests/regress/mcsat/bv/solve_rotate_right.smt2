(set-logic QF_BV)
(set-info :status sat)

(declare-fun s () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (= s #b00111001))
(assert (= ((_ rotate_right 3) x) s))

(check-sat)

(exit)
