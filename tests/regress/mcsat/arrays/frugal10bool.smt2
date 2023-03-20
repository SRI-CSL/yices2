(set-logic QF_AX)

(declare-sort Index 0)
(define-sort Element () Bool)

(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun c () (Array Index Element))
(declare-fun d () (Array Index Element))

(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun i3 () Index)
(declare-fun i4 () Index)
(declare-fun i5 () Index)
(declare-fun i6 () Index)
(declare-fun i7 () Index)
(declare-fun i8 () Index)
(declare-fun i9 () Index)

(declare-fun x0 () Element)
(declare-fun x1 () Element)
(declare-fun x2 () Element)
(declare-fun x3 () Element)
(declare-fun x4 () Element)
(declare-fun x5 () Element)
(declare-fun x6 () Element)
(declare-fun x7 () Element)
(declare-fun x8 () Element)
(declare-fun x9 () Element)

(assert 
 (and 
  (= c (store (store (store (store (store (store (store (store (store (store a i0 x0) i1 x1) i2 x2) i3 x3) i4 x4) i5 x5) i6 x6) i7 x7) i8 x8) i9 x9)) 
  (= d (store (store (store (store (store (store (store (store (store (store b i0 x0) i1 x1) i2 x2) i3 x3) i4 x4) i5 x5) i6 x6) i7 x7) i8 x8) i9 x9))
  (not (= c d))))

(check-sat)
(exit)
