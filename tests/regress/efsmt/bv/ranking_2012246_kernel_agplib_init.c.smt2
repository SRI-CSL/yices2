(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(assert (exists ((c__init__main__1__i_36_C (_ BitVec 8))) (forall ((termination__pre__0__c__init__main__1__i (_ BitVec 8))) (forall ((c__init__main__1__i_35_0 (_ BitVec 8))) (forall ((c__init__main__1__i (_ BitVec 8))) (=> (and (= termination__pre__0__c__init__main__1__i c__init__main__1__i_35_0) (not (= c__init__main__1__i_35_0 (_ bv0 8))) (= c__init__main__1__i ((_ extract 7 0) (bvand ((_ zero_extend 24) c__init__main__1__i_35_0) (bvsub ((_ zero_extend 24) c__init__main__1__i_35_0) (_ bv1 32)))))) (bvslt (bvmul ((_ sign_extend 9) c__init__main__1__i_36_C) ((_ zero_extend 9) c__init__main__1__i)) (bvmul ((_ sign_extend 9) c__init__main__1__i_36_C) ((_ zero_extend 9) termination__pre__0__c__init__main__1__i)))) ) ) ) ))
(check-sat)
(exit)
