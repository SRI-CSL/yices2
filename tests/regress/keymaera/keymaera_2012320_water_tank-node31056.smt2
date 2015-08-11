(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 31056 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore83 () Real)
(declare-fun t36uscore0dollarskuscore3 () Real)
(declare-fun yuscore2dollarskuscore83 () Real)
(declare-fun ts36uscore3 () Real)
(declare-fun xuscore2dollarskuscore73 () Real)
(assert (not (exists ((ts36uscore3 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts36uscore3) (<= ts36uscore3 t36uscore0dollarskuscore3)) (<= (+ ts36uscore3 xuscore2dollarskuscore73) 2)) (>= t36uscore0dollarskuscore3 0)) (> xuscore2dollarskuscore73 2)) (= stuscore2dollarskuscore83 1)) (>= yuscore2dollarskuscore83 1)) (<= yuscore2dollarskuscore83 12)) (>= yuscore2dollarskuscore83 (- 5 (* 2 xuscore2dollarskuscore73)))) (<= yuscore2dollarskuscore83 (+ 10 xuscore2dollarskuscore73))) (<= (+ t36uscore0dollarskuscore3 yuscore2dollarskuscore83) (+ 10 (+ t36uscore0dollarskuscore3 xuscore2dollarskuscore73)))))))
(check-sat)
(exit)
