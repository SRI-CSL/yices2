(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(assert (exists ((c__gsm6102__main__1__l_var_36_C (_ BitVec 32))) (forall ((termination__pre__0__c__gsm6102__main__1__l_var (_ BitVec 32))) (forall ((c__gsm6102__main__1__l_var_35_0 (_ BitVec 32))) (forall ((c__gsm6102__main__1__l_var (_ BitVec 32))) (=> (and (= termination__pre__0__c__gsm6102__main__1__l_var c__gsm6102__main__1__l_var_35_0) (bvslt c__gsm6102__main__1__l_var_35_0 (_ bv1073741824 32)) (= c__gsm6102__main__1__l_var (bvshl c__gsm6102__main__1__l_var_35_0 (_ bv1 32)))) (bvslt (bvmul ((_ sign_extend 32) c__gsm6102__main__1__l_var_36_C) ((_ sign_extend 32) c__gsm6102__main__1__l_var)) (bvmul ((_ sign_extend 32) c__gsm6102__main__1__l_var_36_C) ((_ sign_extend 32) termination__pre__0__c__gsm6102__main__1__l_var)))) ) ) ) ))
(check-sat)
(exit)
