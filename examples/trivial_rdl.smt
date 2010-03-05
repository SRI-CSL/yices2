(benchmark bignum
 :source { SMT-COMP'06 Organizers }
 :notes "This benchmark is designed to check if the DP supports bignumbers."
 :status sat
 :difficulty { 0 }
 :category { check }
 :logic QF_RDL
 :extrafuns ((x1 Real))
 :extrafuns ((x2 Real))
 :extrafuns ((x3 Real))
 :extrafuns ((x4 Real))
 :formula
 (and (<= (- x1 x2) (/ 1 10))
      (<= (- x2 x3) (/ 1 20))
      (<= (- x3 x4) (~ (/ 1 10)))
      (<= (- x4 x1) (~ (/ 1 21)))))
