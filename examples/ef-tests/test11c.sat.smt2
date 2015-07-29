;; test11c.sat.ys converted to the SMT-LIB2 notation
(set-logic BV)

(set-option :yices-ef-max-iters 2049)

(declare-fun y () (_ BitVec 12))
(assert
  (forall ((x0 (_ BitVec 12)))
    (or (not (= (bit y 0) (bit (bvadd x0 x0) 0)))
        (not (= (bit y 1) (bit (bvadd x0 x0) 1)))
        (not (= (bit y 2) (bit (bvadd x0 x0) 2)))
        (not (= (bit y 3) (bit (bvadd x0 x0) 3)))
        (not (= (bit y 4) (bit (bvadd x0 x0) 4)))
        (not (= (bit y 5) (bit (bvadd x0 x0) 5)))
        (not (= (bit y 6) (bit (bvadd x0 x0) 6)))
        (not (= (bit y 7) (bit (bvadd x0 x0) 7)))
        (not (= (bit y 8) (bit (bvadd x0 x0) 8)))
        (not (= (bit y 9) (bit (bvadd x0 x0) 9)))
        (not (= (bit y 10) (bit (bvadd x0 x0) 10)))
        (not (= (bit y 11) (bit (bvadd x0 x0) 11))))))

(check-sat)
(get-model)
