(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 26))
(declare-fun v3 () (_ BitVec 26))
(declare-fun v1 () (_ BitVec 26))
(declare-fun y () (_ BitVec 26))


(define-fun a0 () Bool (bvslt v3 (bvadd (bvmul #b11111111111111111111111111 v0) v1 y)))

(define-fun a1 () Bool (= (bvadd (bvmul #b11111111111111111111111111 v0) v1) y))

(define-fun a2 () Bool (distinct (bvadd #b00000000000000000000000001 (bvmul #b00000000000000000000000010 v0) (bvmul #b11111111111111111111111110 v1) v3) #b00000000000000000000000000))

(define-fun a3 () Bool (bvult (bvadd #b10000000000000000000000000 (bvmul #b11111111111111111111111110 v0) (bvmul #b00000000000000000000000010 v1)) (bvadd #b10000000000000000000000001 v3)))

(assert a0)
(assert a1)
(assert a2)
(assert a3)

(check-sat)
(exit)
