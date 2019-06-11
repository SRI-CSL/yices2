(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
We verify that (x < y) -> (x + 1 <= y)
Contributed by Andreas Froehlich, Gergely Kovasznai, Armin Biere
Institute for Formal Models and Verification, JKU, Linz, 2013
source: http://fmv.jku.at/smtbench and "Efficiently Solving Bit-Vector Problems Using Model Checkers" by Andreas Froehlich, Gergely Kovasznai, Armin Biere. In Proc. 11th Intl. Workshop on Satisfiability Modulo Theories (SMT'13), pages 6-15, aff. to SAT'13, Helsinki, Finland, 2013.
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x () (_ BitVec 29481))
(declare-fun y () (_ BitVec 29481))
(assert (bvult x y))
(assert (bvugt (bvadd x (_ bv1 29481)) y))
(check-sat)
(exit)
