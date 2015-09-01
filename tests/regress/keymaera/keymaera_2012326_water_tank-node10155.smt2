(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 10155 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun yuscore2dollarskuscore11 () Real)
(declare-fun stuscore2dollarskuscore11 () Real)
(declare-fun xuscore2dollarskuscore3 () Real)
(declare-fun t7uscore0dollarskuscore0 () Real)
(declare-fun ts7uscore0 () Real)
(assert (not (exists ((ts7uscore0 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts7uscore0) (<= ts7uscore0 t7uscore0dollarskuscore0)) (<= (+ ts7uscore0 yuscore2dollarskuscore11) 10)) (>= t7uscore0dollarskuscore0 0)) (> yuscore2dollarskuscore11 10)) (= stuscore2dollarskuscore11 0)) (>= yuscore2dollarskuscore11 1)) (<= yuscore2dollarskuscore11 12)) (<= yuscore2dollarskuscore11 (+ 10 xuscore2dollarskuscore3))) (or (= stuscore2dollarskuscore11 3) (>= (+ t7uscore0dollarskuscore0 yuscore2dollarskuscore11) 1))))))
(check-sat)
(exit)
