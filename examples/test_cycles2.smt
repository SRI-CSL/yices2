(benchmark test_cycles2.smt
 :source { 
   Test of yices substitution/preprocessing,
 }
 :logic QF_UF
 :extrafuns ((f U U U) (g U U) (h U U U))
 :extrafuns ((x U) (y U) (z U) (t U) (v U))
 :formula
 (and (= (f (g x) (h y z)) t)
      (= x (h y z))
      (= y (h (g x) (g x)))
      (= z (h (g x) (g x)))))

