(benchmark bv_cycle
:logic QF_BV
:extrafuns ((a BitVec[16]))
:formula
(let (?b (bvmul bv1232[16] a)) (= a ?b)))
