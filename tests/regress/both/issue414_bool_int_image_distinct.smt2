(set-logic ALL)

(declare-fun f0 (Bool) Int)
(declare-fun f1 (Bool) Int)
(declare-fun f2 (Bool) Int)
(declare-fun f3 (Bool) Int)
(declare-fun f4 (Bool) Int)

(assert (distinct f0 f1 f2 f3 f4))

(assert (or (= (f0 true) 0) (= (f0 true) 1)))
(assert (or (= (f0 false) 0) (= (f0 false) 1)))
(assert (or (= (f1 true) 0) (= (f1 true) 1)))
(assert (or (= (f1 false) 0) (= (f1 false) 1)))
(assert (or (= (f2 true) 0) (= (f2 true) 1)))
(assert (or (= (f2 false) 0) (= (f2 false) 1)))
(assert (or (= (f3 true) 0) (= (f3 true) 1)))
(assert (or (= (f3 false) 0) (= (f3 false) 1)))
(assert (or (= (f4 true) 0) (= (f4 true) 1)))
(assert (or (= (f4 false) 0) (= (f4 false) 1)))

(check-sat)
