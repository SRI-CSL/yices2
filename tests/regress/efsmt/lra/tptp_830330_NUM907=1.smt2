(set-logic LRA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(assert (not (exists ((?X Real) (?Y Real) (?Z Real)) (= (= (+ ?X ?Y) ?Z) (and (= (- ?Z ?Y) ?X) (= (- ?Z ?X) ?Y))))))
(check-sat)
(exit)
