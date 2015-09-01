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

(define-fun mk-bit ((x Bool)) (_ BitVec 1) 
   (ite x #b1 #b0))

(assert
 (exists ((y6 Bool)
	  (y7 Bool)
	  (y8 Bool)
	  (y9 Bool)
	  (y10 Bool)
	  (y11 Bool))
	 (let ((y (concat (mk-bit y11) (mk-bit y10) (mk-bit y9) (mk-bit y8) (mk-bit y7) (mk-bit y6)
			  (mk-bit y5) (mk-bit y4) (mk-bit y3) (mk-bit y2) (mk-bit y1) (mk-bit y0))))
	   (forall ((x0 (_ BitVec 12))) (not (= y (bvadd x0 x0)))))))

(check-sat)
(get-model)


