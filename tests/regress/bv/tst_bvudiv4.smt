(benchmark tst_bvudiv4
 :logic QF_BV
 :extrafuns ((a BitVec[80]))
 :extrafuns ((b BitVec[80]))
 :formula 
  (and (= a (bvudiv bv999[80] bv1000[80]))
       (= b (bvurem bv999[80] bv1000[80])))
)
