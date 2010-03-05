(benchmark tst_bvudiv3
 :logic QF_BV
 :extrafuns ((a BitVec[80]))
 :extrafuns ((b BitVec[80]))
 :formula 
  (and (= a (bvudiv bv999[80] bv27[80]))
       (= b (bvurem bv999[80] bv27[80])))
)
