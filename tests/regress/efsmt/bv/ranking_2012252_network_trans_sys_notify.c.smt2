(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(assert (exists ((c__notify__main__1__currentOffset_36_C (_ BitVec 32))) (forall ((termination__pre__0__c__notify__main__1__currentOffset (_ BitVec 32))) (forall ((c__notify__main__1__streamLength (_ BitVec 32))) (forall ((c__notify__main__1__subStreamLength (_ BitVec 32))) (forall ((c__notify__main__1__currentOffset_35_0 (_ BitVec 32))) (forall ((c__notify__main__1__currentOffset (_ BitVec 32))) (=> (and (= termination__pre__0__c__notify__main__1__currentOffset c__notify__main__1__currentOffset_35_0) (bvuge c__notify__main__1__streamLength (bvadd c__notify__main__1__currentOffset_35_0 c__notify__main__1__subStreamLength)) (= c__notify__main__1__currentOffset (bvadd c__notify__main__1__currentOffset_35_0 c__notify__main__1__subStreamLength))) (bvslt (bvmul ((_ sign_extend 33) c__notify__main__1__currentOffset_36_C) ((_ zero_extend 33) c__notify__main__1__currentOffset)) (bvmul ((_ sign_extend 33) c__notify__main__1__currentOffset_36_C) ((_ zero_extend 33) termination__pre__0__c__notify__main__1__currentOffset)))) ) ) ) ) ) ))
(check-sat)
(exit)
