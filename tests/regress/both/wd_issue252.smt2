(set-logic QF_ALIA)

(declare-fun x237 () (Array (Array (Array Bool Bool) (Array Bool Bool)) (Array (Array Bool Bool) Bool)))
(declare-fun x385 () (Array Bool Bool))
(declare-fun x547 () (Array Bool Bool))
(declare-fun x569 () (Array (Array (Array Bool Bool) (Array Bool Bool)) (Array (Array Bool Bool) Bool)))
(declare-fun x600 () (Array (Array (Array Bool Bool) (Array Bool Bool)) (Array (Array Bool Bool) Bool)))
(declare-fun x619 () (Array (Array Bool Bool) (Array Bool Bool)))
(declare-fun x622 () (Array Bool Bool))

(declare-const A (Array (Array Bool Bool) (Array Bool Bool)))
(declare-const B (Array (Array Bool Bool) Bool))

(assert (=  x237
	    (store x600 A (store B x547 true))
	    (store (store (store x569 A (store B x385 true)) x619 B) A (store B (select A x622) true))
))

(check-sat)
