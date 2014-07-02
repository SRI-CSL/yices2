(benchmark tst_bvmodel2
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:extrafuns ((d BitVec[16]))
:extrafuns ((x BitVec[8]))
:assumption (= a (bvor b c))
:assumption (= d (bvmul a bv23[16]))
:assumption (bvuge (extract[7:0] d) bv10[8])
:assumption (= b (sign_extend[8] x))
:assumption (= (extract[7:7] x) bv1[1])
)
