(set-option :produce-unsat-model-interpolants true)
(set-logic QF_BV)

(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun y!0 () (_ BitVec 32))
(declare-fun y!1 () (_ BitVec 32))
(declare-fun y!2 () (_ BitVec 32))
(declare-fun y!3 () (_ BitVec 32))
(declare-fun forall_placeholder3 () Bool)
(declare-fun forall_placeholder2 () Bool)
(declare-fun forall_placeholder1 () Bool)
(declare-fun forall_placeholder0 () Bool)
(declare-fun y!4 () (_ BitVec 32))
(declare-fun y!5 () (_ BitVec 32))
(declare-fun y!6 () (_ BitVec 32))
(declare-fun y!7 () (_ BitVec 32))
(declare-fun forall_placeholder6 () Bool)
(declare-fun forall_placeholder5 () Bool)
(declare-fun forall_placeholder4 () Bool)

(assert forall_placeholder4)

(assert
 (or
  forall_placeholder6
  (or
   (or
    (bvsge
     (bvadd
      (bvmul #b00000000000000000000000001011011 y!7)
      (bvadd
       (bvmul #b11111111111111111111111110100000 y!5)
       (bvmul #b00000000000000000000000000111000 y!4)))
     #b00000000000000000000000000100010)
    (not
     (bvsge
      #b00000000000000000000000000100100
      (bvadd
       (bvmul #b11111111111111111111111111100000 y!7)
       (bvadd
        (bvmul #b00000000000000000000000000011000 y!6)
        (bvadd
         (bvmul #b00000000000000000000000001011000 y!5)
         (bvmul #b00000000000000000000000000011010 y!4)))))))
   (not
    (or
     (not
      (bvsge
       #b11111111111111111111111111100111
       (bvadd
        (bvmul #b00000000000000000000000000111111 y!6)
        (bvadd
         (bvmul #b11111111111111111111111111111101 y!5)
         (bvmul #b00000000000000000000000000011101 y!4)))))
     (not
      (bvsge
       #b11111111111111111111111111100001
       (bvadd
        (bvmul #b00000000000000000000000000001011 y!7)
        (bvadd
         (bvmul #b11111111111111111111111111110100 y!6)
         (bvadd
          (bvmul #b11111111111111111111111110101110 y!5)
          (bvmul #b00000000000000000000000001011010 y!4)))))))))))

(assert (or forall_placeholder5 forall_placeholder6))

(assert (or forall_placeholder4 forall_placeholder5))

(assert
 (or
  (not forall_placeholder4)
  (bvsge
   #b00000000000000000000000000100100
   (bvadd
    (bvmul #b00000000000000000000000000011010 y!4)
    #b01100000000000000000000000000000))))

(assert
 (or
  (not forall_placeholder4)
  (bvsge
   #b00000000000000000000000000100100
   (bvmul #b00000000000000000000000000011010 y!4))))

(assert
 (or
  (not forall_placeholder4)
  (bvsge
   #b00000000000000000000000000100100
   (bvadd
    (bvmul #b00000000000000000000000000011010 y!4)
    #b11000000000000000000000000000000))))

(check-sat-assuming-model
 (forall_placeholder0
  forall_placeholder1
  forall_placeholder2
  forall_placeholder3
  y!3
  y!2
  y!1
  y!0
  x4
  x3
  x2
  x1)
 (true
  true
  false
  true
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000
  #b00000000000000000000000000000000))

(get-unsat-model-interpolant)
