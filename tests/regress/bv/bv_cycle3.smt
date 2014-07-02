(benchmark bv_cycle3
:logic QF_BV
:extrafuns ((a BitVec[16]))
:extrafuns ((b BitVec[16]))
:extrafuns ((c BitVec[16]))
:formula
(let (?u (bvadd a b))
(let (?v (bvmul ?u ?u))
(let (?x (bvadd ?v (bvmul bv3[16] c)))
(and (= a ?v) (bvugt ?x bv0[16]))))))

