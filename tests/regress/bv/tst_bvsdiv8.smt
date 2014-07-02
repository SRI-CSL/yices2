(benchmark tst_bvsdiv8
 :logic QF_BV
 :extrafuns ((a BitVec[4]))
 :extrafuns ((b BitVec[4]))
 :extrafuns ((c BitVec[4]))
 :formula
  (and (= a (bvsdiv bvbin1010 bvbin1101))
       (= b (bvsrem bvbin1010 bvbin1101))
       (= c (bvsmod bvbin1010 bvbin1101)))
)
