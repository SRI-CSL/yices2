(set-logic QF_AUFLIA)
(set-info :source |
Translated from old SVC processor verification benchmarks.  Contact Clark
Barrett at barrett@cs.nyu.edu for more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun opsel (Int) Int)
(declare-fun icache () (Array Int Int))
(declare-fun PC (Int) Int)
(declare-fun s_0 () Int)
(declare-fun selDest (Int) Int)
(declare-fun RF (Int) (Array Int Int))
(declare-fun s__1 () Int)
(declare-fun dcache (Int) (Array Int Int))
(declare-fun regAsel (Int) Int)
(declare-fun fb_var_13 (Int) Int)
(declare-fun squash_0 (Int) Bool)
(declare-fun IR1 (Int) Int)
(declare-fun t__1 () Int)
(declare-fun fb_var_6 (Int) Int)
(declare-fun t_0 () Int)
(declare-fun stall_0 (Int) Bool)
(declare-fun fb_var_7 (Int) Bool)
(assert (let ((?v_5 (RF s_0)) (?v_18 (dcache s_0)) (?v_8 (fb_var_13 (+ 1 s_0))) (?v_2 (RF s__1)) (?v_17 (fb_var_13 s_0)) (?v_30 (= (opsel 13) 13)) (?v_37 (= (selDest 13) 13)) (?v_25 (RF t_0)) (?v_27 (fb_var_6 (+ 1 t_0))) (?v_21 (RF t__1)) (?v_9 (+ (- 1) s_0))) (let ((?v_1 (select icache (PC ?v_9)))) (let ((?v_0 (opsel ?v_1)) (?v_3 (selDest ?v_1))) (let ((?v_4 (ite (= ?v_0 10) true (ite (= ?v_0 11) true (ite (= ?v_0 12) true (= ?v_3 13))))) (?v_6 (= ?v_0 14)) (?v_7 (regAsel ?v_1)) (?v_11 (ite (squash_0 ?v_9) 13 (select icache (PC (+ (- 2) s_0)))))) (let ((?v_10 (opsel ?v_11))) (let ((?v_14 (= ?v_10 10)) (?v_13 (selDest ?v_11)) (?v_12 (RF ?v_9)) (?v_15 (dcache ?v_9)) (?v_16 (regAsel ?v_11)) (?v_38 (+ (- 1) t__1))) (let ((?v_20 (IR1 ?v_38))) (let ((?v_19 (opsel ?v_20)) (?v_22 (selDest ?v_20)) (?v_28 (+ (- 1) t_0))) (let ((?v_24 (IR1 ?v_28))) (let ((?v_23 (opsel ?v_24)) (?v_26 (selDest ?v_24)) (?v_31 (stall_0 ?v_28)) (?v_29 (+ (- 2) t_0))) (let ((?v_32 (IR1 ?v_29))) (let ((?v_34 (ite ?v_31 13 ?v_32))) (let ((?v_33 (opsel ?v_34)) (?v_36 (selDest ?v_34)) (?v_35 (RF ?v_28))) (not (ite (ite (ite (= (ite ?v_4 ?v_2 (store ?v_2 ?v_3 (ite ?v_6 (select (dcache s__1) ?v_7) ?v_8))) (ite ?v_4 ?v_5 (store ?v_5 ?v_3 (ite ?v_6 (select ?v_18 ?v_7) ?v_8)))) false true) (ite (ite (= (ite (ite ?v_14 true (ite (= ?v_10 11) true (ite (= ?v_10 12) true (= ?v_13 13)))) ?v_12 (store ?v_12 ?v_13 (ite (= ?v_10 14) (select ?v_15 ?v_16) ?v_17))) ?v_5) (ite ?v_30 (ite ?v_37 (ite (= (ite ?v_14 (store ?v_15 ?v_16 ?v_17) ?v_15) ?v_18) (ite (ite (squash_0 (+ (- 1) s__1)) false true) (ite (squash_0 s__1) (= s__1 ?v_9) (= s__1 s_0)) false) false) false) false) false) false true) true) (ite (ite (= (ite (ite (= ?v_19 10) true (ite (= ?v_19 11) true (ite (= ?v_19 12) true (= ?v_22 13)))) ?v_21 (store ?v_21 ?v_22 ?v_27)) (ite (ite (= ?v_23 10) true (ite (= ?v_23 11) true (ite (= ?v_23 12) true (= ?v_26 13)))) ?v_25 (store ?v_25 ?v_26 ?v_27))) false true) (ite (ite (= (ite ?v_31 ?v_32 (ite (fb_var_7 ?v_28) 13 (select icache (PC ?v_29)))) ?v_24) (ite ?v_30 (ite (= (ite (ite (= ?v_33 10) true (ite (= ?v_33 11) true (ite (= ?v_33 12) true (= ?v_36 13)))) ?v_35 (store ?v_35 ?v_36 (fb_var_6 t_0))) ?v_25) (ite ?v_37 (ite (ite (stall_0 ?v_38) false true) (ite (stall_0 t__1) (= t__1 ?v_28) (= t__1 t_0)) false) false) false) false) false) false true) true) false))))))))))))))))
(check-sat)
(exit)
