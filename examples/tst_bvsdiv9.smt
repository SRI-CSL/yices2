(benchmark tst_bvsdiv9
 :logic QF_BV
 :extrafuns ((a BitVec[80]))
 :extrafuns ((b BitVec[80]))
 :extrafuns ((c BitVec[80]))
 :formula 
  (and (= a (bvsdiv bv999[80] bv0[80]))
       (= b (bvsrem bv999[80] bv0[80]))
       (= c (bvsmod bv999[80] bv0[80])))
)
