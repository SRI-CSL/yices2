(benchmark integerTest.smt
:source {
Tight parallelogram with no integer solution
by Jochen Hoenicke
}
:status unsat
:difficulty { 0 }
:logic QF_LIA
:extrafuns ((x Int))
:extrafuns ((y Int))
:formula
(and (<= 0 (- (* 428300 x) (* 324501 y)))
     (<= (- (* 428300 x) (* 324501 y)) 99)
     (<= 1 (- (* 428301 x) (* 324500 y)))
     (<= (- (* 428301 x) (* 324500 y)) 100))
)
