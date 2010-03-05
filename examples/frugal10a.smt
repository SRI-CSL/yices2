(benchmark frugal10a
  :source {
   test for Yices (taken from SMT 2008 paper by Sava Krstic et al.)
  }
  :status unsat
  :category { crafted }
  :logic QF_AX
  :extrafuns ((a Array))
  :extrafuns ((b Array))
  :extrafuns ((c Array))
  :extrafuns ((d Array))
  :extrafuns ((i0 Index))
  :extrafuns ((i1 Index))
  :extrafuns ((i2 Index))
  :extrafuns ((i3 Index))
  :extrafuns ((i4 Index))
  :extrafuns ((i5 Index))
  :extrafuns ((i6 Index))
  :extrafuns ((i7 Index))
  :extrafuns ((i8 Index))
  :extrafuns ((i9 Index))
  :extrafuns ((x0 Element))
  :extrafuns ((x1 Element))
  :extrafuns ((x2 Element))
  :extrafuns ((x3 Element))
  :extrafuns ((x4 Element))
  :extrafuns ((x5 Element))
  :extrafuns ((x6 Element))
  :extrafuns ((x7 Element))
  :extrafuns ((x8 Element))
  :extrafuns ((x9 Element))
  :formula 
 (and 
  (= c (store (store (store (store (store (store (store (store (store (store a i0 x0) i1 x1) i2 x2) i3 x3) i4 x4) i5 x5) i6 x6) i7 x7) i8 x8) i9 x9))
  (= d (store (store (store (store (store (store (store (store (store (store b i0 x0) i1 x1) i2 x2) i3 x3) i4 x4) i5 x5) i6 x6) i7 x7) i8 x8) i9 x9))
  (not (= c d)))

)
