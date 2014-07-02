(benchmark tst_bvmodel
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:extrafuns ((x BitVec[8]))
:assumption (= a (bvor b c))
:assumption (bvuge (extract[7:0] a) bv10[8])
:assumption (= b (sign_extend[8] x))
:assumption (= (extract[7:7] x) bv1[1])
)
