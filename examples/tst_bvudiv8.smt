(benchmark tst_bvudiv8
 :logic QF_BV
 :extrafuns ((a BitVec[4])) 
 :extrafuns ((b BitVec[4]))
 :extrafuns ((c BitVec[4]))
 :formula
  (and (= b (bvudiv a bvbin0101))
       (= c (bvurem a bvbin0101))
       (bvugt c bvbin0010)))
)
