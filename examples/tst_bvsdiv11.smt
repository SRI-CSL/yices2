(benchmark tst_bvsdiv11
 :logic QF_BV
 :extrafuns ((a BitVec[8]))
 :extrafuns ((b BitVec[8]))
 :extrafuns ((c BitVec[8]))
 :formula 
  (and (= a (bvsdiv bvbin00110011 bv0[8]))
       (= b (bvsrem bvbin00110011 bv0[8]))
       (= c (bvsmod bvbin00110011 bv0[8])))
)
