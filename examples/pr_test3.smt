(benchmark test_bvurm_lt
:logic QF_BV
:extrafuns ((v1 BitVec[32]))
:extrafuns ((v2 BitVec[32]))
:extrafuns ((v3 BitVec[32]))

:formula (and (not (= v1 bvhex00000000))
              (= v3 (bvurem v2 v1))
              (not (bvult v3 v1)))
)

