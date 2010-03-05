(benchmark tst_bvudiv6
 :logic QF_BV
 :extrafuns ((a BitVec[4])) 
 :extrafuns ((b BitVec[4]))
 :extrafuns ((c BitVec[4]))
 :formula
  (and (= b (bvudiv a bvbin0101))
       (= c (bvudiv b bvbin0101)))
)
