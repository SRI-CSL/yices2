(benchmark bv_pprod2
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:extrafuns ((d BitVec[16]))
:assumption (= bv0[16] (bvmul a a a a b b b c c d)))
