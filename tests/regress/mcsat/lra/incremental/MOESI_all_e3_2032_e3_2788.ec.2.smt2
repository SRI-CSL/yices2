(set-logic QF_LRA)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun x () Real)

(assert (= x (ite a (- 1) 0)))
(assert (= (= 1 x) a))
(assert (= (and (= x 0) (not a)) c))
(assert d)

(push 1)

(assert (not c))

(check-sat)

(pop 1)

(assert (not b))

(check-sat)

(exit)
