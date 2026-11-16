(set-logic QF_UFBV)
; No uninterpreted function: bit-vector solver without the egraph
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-value (x))
