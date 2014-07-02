(benchmark bv_pprod1
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:assumption (= bv0[16] (bvmul (bvmul a a) (bvmul b b) (bvmul c c)))
)