(benchmark tst_bvsdiv6
 :logic QF_BV
 :extrafuns ((a BitVec[4]))
 :extrafuns ((b BitVec[4]))
 :extrafuns ((c BitVec[4]))
 :formula
  (and (= a (bvsdiv bvbin1010 bvbin0011))
       (= b (bvsrem bvbin1010 bvbin0011))
       (= c (bvsmod bvbin1010 bvbin0011)))
)
