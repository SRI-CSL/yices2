(benchmark test_cycles1.smt
 :source { 
   Test of yices substitution/preprocessing,
 }
 :logic QF_UF
 :extrafuns ((f U U U) (g U U) (h U U U))
 :extrafuns ((x U) (y U) (z U) (t U) (v U))
 :formula
 (and (= (f (g x) (h y z)) t)
      (= x (f y v))
      (= y (f z (g v)))
      (= v (h (g x) (g y)))))

