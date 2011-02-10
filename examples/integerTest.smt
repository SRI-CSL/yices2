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
(and (<= 0 (- (* 4283000000 x) (* 3245000001 y)))
     (<= (- (* 4283000000 x) (* 3245000001 y)) 999999)
     (<= 1 (- (* 4283000001 x) (* 3245000000 y)))
     (<= (- (* 4283000001 x) (* 3245000000 y)) 1000000))
)
