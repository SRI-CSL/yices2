(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status sat)
(assert (not (exists ((?X Int) (?Y Int) (?Z1 Int) (?Z2 Int)) (let ((?v_0 (+ ?X ?Y))) (and (= ?v_0 ?Z1) (= ?v_0 ?Z2) (not (= ?Z1 ?Z2)))))))
(check-sat)
(exit)
