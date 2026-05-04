(set-logic ALL)

(declare-fun f0 (Bool) Bool)
(declare-fun f1 (Bool) Bool)
(declare-fun f2 (Bool) Bool)
(declare-fun f3 (Bool) Bool)
(declare-fun f4 (Bool) Bool)

(assert (distinct f0 f1 f2 f3 f4))

(check-sat)
