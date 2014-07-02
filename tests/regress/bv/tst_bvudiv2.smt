(benchmark tst_bvudiv2
 :logic QF_BV
 :extrafuns ((a BitVec[4]))
 :extrafuns ((b BitVec[4]))
 :formula 
  (and (= a (bvudiv bvbin1000 bvbin0110))
       (= b (bvurem bvbin1000 bvbin0110)))
)
