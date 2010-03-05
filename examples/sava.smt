(benchmark sava
  :source {
   test for Yices (taken from SMT 2008 paper by Sava et al.)   
  }
  :status unsat
  :difficulty { 0 }
  :category { crafted }
  :logic QF_AX
  :extrafuns ((a Array))
  :extrafuns ((b Array))
  :extrafuns ((f Array Element))
  :extrafuns ((i Index))
  :extrafuns ((j Index))
  :extrafuns ((x Element))
  :extrafuns ((y Element))
  :assumption
   (= b (store a i x))
  :assumption
   (= b (store a j y))
  :assumption (not (= i j))
  :formula (not (= (f a) (f b)))
)
