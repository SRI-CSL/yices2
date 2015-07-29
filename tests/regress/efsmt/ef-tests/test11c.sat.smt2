;; test11c.sat.ys converted to the SMT-LIB2 notation
(set-logic BV)

(set-option :yices-ef-max-iters 2049)

(declare-fun y () (_ BitVec 12))
(assert
  (forall ((x0 (_ BitVec 12)))
    (or (not (= ((_ extract 1 0) y) ((_ extract 1 0) (bvadd x0 x0))))
        (not (= ((_ extract 2 1) y) ((_ extract 2 1) (bvadd x0 x0))))   
        (not (= ((_ extract 3 2) y) ((_ extract 3 2) (bvadd x0 x0))))   
        (not (= ((_ extract 4 3) y) ((_ extract 4 3) (bvadd x0 x0))))   
        (not (= ((_ extract 5 4) y) ((_ extract 5 4) (bvadd x0 x0))))   
        (not (= ((_ extract 6 5) y) ((_ extract 6 5) (bvadd x0 x0))))   
        (not (= ((_ extract 7 6) y) ((_ extract 7 6) (bvadd x0 x0))))   
        (not (= ((_ extract 8 7) y) ((_ extract 8 7) (bvadd x0 x0))))   
        (not (= ((_ extract 9 8) y) ((_ extract 9 8) (bvadd x0 x0))))   
        (not (= ((_ extract 10 9) y) ((_ extract 10 9) (bvadd x0 x0)))))))

(check-sat)
