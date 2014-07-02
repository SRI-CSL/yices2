(benchmark tst_bvsdiv12
 :logic QF_BV
 :extrafuns ((a BitVec[8]))
 :extrafuns ((b BitVec[8]))
 :extrafuns ((c BitVec[8]))
 :formula 
  (and (= a (bvsdiv bvbin10110011 bv0[8]))
       (= b (bvsrem bvbin10110011 bv0[8]))
       (= c (bvsmod bvbin10110011 bv0[8])))
)
