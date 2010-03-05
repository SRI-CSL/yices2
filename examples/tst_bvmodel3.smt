(benchmark tst_bvmodel3
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:extrafuns ((d BitVec[16]))
:extrafuns ((x BitVec[8]))
:extrapreds ((p))
:assumption (= p (bvuge a b))
:assumption (bvuge a c)
:assumption (bvuge c b)
:assumption (= x (ite p x (extract[7:0] d)))
)
