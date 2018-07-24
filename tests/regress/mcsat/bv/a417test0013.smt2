(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun utf8_0 () (_ BitVec 8))
(declare-fun utf8_1 () (_ BitVec 8))
(assert (bvslt (concat (_ bv0 24) ((_ extract 7 0) utf8_0)) (_ bv128 32)))
(assert (not (bvslt (concat (_ bv0 24) ((_ extract 7 0) utf8_0)) (_ bv32 32))))
(assert (not (bvsle (_ bv127 32) (concat (_ bv0 24) ((_ extract 7 0) utf8_0)))))
(assert (not (= (concat (_ bv0 24) ((_ extract 7 0) utf8_0)) (_ bv38 32))))
(assert (not (bvslt (concat (_ bv0 24) ((_ extract 7 0) utf8_1)) (_ bv128 32))))
(assert (not (bvslt (concat (_ bv0 24) ((_ extract 7 0) utf8_1)) (_ bv194 32))))
(assert (bvslt (concat (_ bv0 24) ((_ extract 7 0) utf8_1)) (_ bv224 32)))
(check-sat)
(exit)
