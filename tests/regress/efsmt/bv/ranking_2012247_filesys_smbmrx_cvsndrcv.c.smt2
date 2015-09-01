(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(assert (exists ((c__cvsndrcv__main__1__len_36_C (_ BitVec 32))) (forall ((termination__pre__1__c__cvsndrcv__main__1__len (_ BitVec 32))) (forall ((termination__nondet2 (_ BitVec 32))) (forall ((termination__nondet1 (_ BitVec 32))) (forall ((c__cvsndrcv__main__1__len_35_0 (_ BitVec 32))) (forall ((c__main___36_tmp__return_value_nondet_36_2 (_ BitVec 32))) (forall ((c__cvsndrcv__main__1__len (_ BitVec 32))) (=> (and (= termination__pre__1__c__cvsndrcv__main__1__len c__cvsndrcv__main__1__len_35_0) (bvslt c__cvsndrcv__main__1__len_35_0 (_ bv16 32)) (= c__cvsndrcv__main__1__len termination__nondet1) (= c__main___36_tmp__return_value_nondet_36_2 termination__nondet2) (= c__main___36_tmp__return_value_nondet_36_2 (_ bv0 32))) (bvslt (bvmul ((_ sign_extend 32) c__cvsndrcv__main__1__len_36_C) ((_ sign_extend 32) c__cvsndrcv__main__1__len)) (bvmul ((_ sign_extend 32) c__cvsndrcv__main__1__len_36_C) ((_ sign_extend 32) termination__pre__1__c__cvsndrcv__main__1__len)))) ) ) ) ) ) ) ))
(check-sat)
(exit)
