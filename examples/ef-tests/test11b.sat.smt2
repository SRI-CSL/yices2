;; test11b.sat.ys converted to the SMT-LIB2 notation
(set-logic BV)

(set-option :yices-ef-max-iters 2048)
(set-option :yices-ef-gen-mode projection)
(set-option :yices-ef-flatten-iff False)

(declare-fun y0 () Bool)
(declare-fun y1 () Bool)
(declare-fun y2 () Bool)
(declare-fun y3 () Bool)
(declare-fun y4 () Bool)
(declare-fun y5 () Bool)
(declare-fun y6 () Bool)
(declare-fun y7 () Bool)
(declare-fun y8 () Bool)
(declare-fun y9 () Bool)
(declare-fun y10 () Bool)
(declare-fun y11 () Bool)

(assert 
 (let ((y (bool-to-bv y11 y10 y9 y8 y7 y6 y5 y4 y3 y2 y1 y0)))
   (forall ((x0 (_ BitVec 12))) (not (= y (bvadd x0 x0))))))

(check-sat)
(get-model)


