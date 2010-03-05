(benchmark trivial_ax3
  :source {
   test for Yices model construction
  }
  :status sat
  :category { crafted }
  :logic QF_AX
  :extrafuns ((a Array))
  :extrafuns ((i0 Index))
  :extrafuns ((i1 Index))
  :extrafuns ((i2 Index))
  :extrafuns ((x0 Element))
  :extrafuns ((x1 Element))
  :extrafuns ((x2 Element))
  :assumption (distinct i0 i1 i2)
  :formula (= a (store (store (store a i0 x0) i1 x1) i2 x2))

)
