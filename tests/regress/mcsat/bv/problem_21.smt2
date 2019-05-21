(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
    Sequential equivalence checking.
    Calypto Design Systems, Inc. <www.calypto.com>
  |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun P_2 () (_ BitVec 3))
(declare-fun P_3 () (_ BitVec 1))
(declare-fun P_4 () (_ BitVec 28))
(declare-fun P_5 () (_ BitVec 96))
(assert (let ((?v_0 (ite (= (_ bv1 1) P_3) (_ bv0 28) P_4))) (let ((?v_2 (concat (_ bv0 1) ((_ extract 27 0) (ite (= (_ bv1 1) (ite (bvsle (_ bv0 28) ?v_0) (_ bv1 1) (_ bv0 1))) ((_ sign_extend 1) ?v_0) (bvsub (_ bv0 29) (concat ((_ extract 27 27) ?v_0) ?v_0))))))) (let ((?v_1 ((_ extract 28 28) ?v_2)) (?v_10 ((_ extract 47 32) P_5)) (?v_3 ((_ extract 1 1) P_2))) (let ((?v_4 (ite (= ?v_3 (_ bv0 1)) false true)) (?v_5 (ite (= ((_ extract 2 2) P_2) (_ bv0 1)) false true))) (let ((?v_12 (or ?v_4 ?v_5))) (let ((?v_6 (concat (concat (ite (not ?v_12) (_ bv1 1) (_ bv0 1)) ?v_3) (ite (and (not ?v_4) ?v_5) (_ bv1 1) (_ bv0 1))))) (let ((?v_8 (ite (= ?v_6 (_ bv4 3)) (_ bv1 1) (_ bv0 1)))) (let ((?v_9 (concat ?v_8 (ite (= ?v_6 (_ bv1 3)) (_ bv1 1) (_ bv0 1)))) (?v_7 (concat ?v_8 (ite (= ?v_6 (_ bv2 3)) (_ bv1 1) (_ bv0 1))))) (let ((?v_11 (concat (bvxor ((_ extract 1 1) ?v_7) ((_ extract 0 0) ?v_7)) (bvxor ((_ extract 1 1) ?v_9) ((_ extract 0 0) ?v_9))))) (not (= (ite (= (_ bv1 1) (ite (= P_2 (_ bv1 3)) (_ bv1 1) (_ bv0 1))) ((_ sign_extend 49) ((_ extract 14 0) (bvlshr (bvmul (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat ?v_1 ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_1) ?v_2) (concat (_ bv0 28) ?v_10)) (_ bv29 44)))) (_ bv0 64)) (concat (_ bv0 50) (bvand ((_ extract 42 29) (bvmul (concat (_ bv0 27) (ite (= (_ bv3 2) ?v_11) ?v_10 (ite (= (_ bv2 2) ?v_11) ((_ extract 31 16) P_5) (ite (= (_ bv1 2) ?v_11) ((_ extract 15 0) P_5) (_ bv0 16))))) (concat (_ bv0 15) ((_ extract 27 0) ?v_2)))) ((_ extract 13 0) ((_ sign_extend 24) (ite (not (or ?v_12 (not (ite (= ((_ extract 0 0) P_2) (_ bv0 1)) false true)))) (_ bv1 1) (_ bv0 1))))))))))))))))))
(check-sat)
(exit)
