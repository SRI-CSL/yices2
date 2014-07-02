(benchmark tst_bvsdiv10
 :logic QF_BV
 :extrafuns ((a BitVec[80]))
 :extrafuns ((b BitVec[80]))
 :extrafuns ((c BitVec[80]))
 :formula 
  (and (= a (bvsdiv (bvneg bv999[80]) bv0[80]))
       (= b (bvsrem (bvneg bv999[80]) bv0[80]))
       (= c (bvsmod (bvneg bv999[80]) bv0[80])))
)
