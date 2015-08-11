(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(assert (exists ((cpp__main__c__main__1__nSearchIndex_36_C (_ BitVec 32))) (forall ((termination__pre__0__cpp__main__c__main__1__nSearchIndex (_ BitVec 32))) (forall ((cpp__main__c__main__1__stBDList_nTail (_ BitVec 32))) (forall ((cpp__main__c__main__1__nSearchIndex_35_0 (_ BitVec 32))) (forall ((termination__nondet1 (_ BitVec 32))) (forall ((c__main___36_tmp__return_value_nondet_36_1 (_ BitVec 32))) (forall ((cpp__main__c__main__1__nSearchIndex (_ BitVec 32))) (=> (and (= termination__pre__0__cpp__main__c__main__1__nSearchIndex cpp__main__c__main__1__nSearchIndex_35_0) (= c__main___36_tmp__return_value_nondet_36_1 termination__nondet1) (= c__main___36_tmp__return_value_nondet_36_1 (_ bv0 32)) (= cpp__main__c__main__1__nSearchIndex (bvand (bvadd cpp__main__c__main__1__nSearchIndex_35_0 (_ bv1 32)) (_ bv31 32))) (not (= cpp__main__c__main__1__nSearchIndex cpp__main__c__main__1__stBDList_nTail))) (bvslt (bvmul ((_ sign_extend 32) cpp__main__c__main__1__nSearchIndex_36_C) ((_ sign_extend 32) cpp__main__c__main__1__nSearchIndex)) (bvmul ((_ sign_extend 32) cpp__main__c__main__1__nSearchIndex_36_C) ((_ sign_extend 32) termination__pre__0__cpp__main__c__main__1__nSearchIndex)))) ) ) ) ) ) ) ))
(check-sat)
(exit)
