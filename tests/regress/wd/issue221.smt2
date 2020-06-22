(set-logic QF_ABV)
(declare-fun x113 () Bool)
(declare-const v3 Bool)
(declare-const arr0 (Array (_ BitVec 12) (_ BitVec 12)))
(declare-const arr1 (Array (_ BitVec 12) (_ BitVec 12)))
(assert (or x113 v3))
(assert (= true
	   (and
	    (= (store arr0 #x349 #x349) arr1)
	    (distinct (select arr1 #x349) (_ bv0 12) #x349))
	   (= (select arr1 #x349) #x349)
	   v3))
(check-sat)
(exit)
