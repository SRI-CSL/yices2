(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun T1_587 () (_ BitVec 8))
(assert (and true (= T1_587 (_ bv0 8)) (= T1_587 (_ bv110 8))))
(check-sat)
(exit)
