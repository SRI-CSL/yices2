(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 23091 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore40 () Real)
(declare-fun t25uscore0dollarskuscore3 () Real)
(declare-fun yuscore2dollarskuscore48 () Real)
(declare-fun ts25uscore3 () Real)
(declare-fun stuscore2dollarskuscore48 () Real)
(assert (not (exists ((ts25uscore3 Real)) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore48 1) (=> (and (<= 0 ts25uscore3) (<= ts25uscore3 t25uscore0dollarskuscore3)) (<= (+ ts25uscore3 yuscore2dollarskuscore48) 10))) (>= t25uscore0dollarskuscore3 0)) (> yuscore2dollarskuscore48 10)) (= stuscore2dollarskuscore48 0)) (>= yuscore2dollarskuscore48 1)) (<= yuscore2dollarskuscore48 12)) (>= yuscore2dollarskuscore48 (- 5 (* 2 xuscore2dollarskuscore40)))) (<= yuscore2dollarskuscore48 (+ 10 xuscore2dollarskuscore40))) (<= (+ t25uscore0dollarskuscore3 yuscore2dollarskuscore48) (+ 10 (+ t25uscore0dollarskuscore3 xuscore2dollarskuscore40)))))))
(check-sat)
(exit)
