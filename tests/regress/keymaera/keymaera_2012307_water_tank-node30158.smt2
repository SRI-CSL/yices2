(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 30158 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore66 () Real)
(declare-fun ts35uscore3 () Real)
(declare-fun t35uscore0dollarskuscore3 () Real)
(declare-fun stuscore2dollarskuscore76 () Real)
(declare-fun yuscore2dollarskuscore76 () Real)
(assert (not (exists ((ts35uscore3 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts35uscore3) (<= ts35uscore3 t35uscore0dollarskuscore3)) (<= (+ ts35uscore3 xuscore2dollarskuscore66) 2)) (>= t35uscore0dollarskuscore3 0)) (< xuscore2dollarskuscore66 2)) (= stuscore2dollarskuscore76 1)) (>= yuscore2dollarskuscore76 1)) (<= yuscore2dollarskuscore76 12)) (>= yuscore2dollarskuscore76 (- 5 (* 2 xuscore2dollarskuscore66)))) (<= yuscore2dollarskuscore76 (+ 10 xuscore2dollarskuscore66))) (<= (+ t35uscore0dollarskuscore3 yuscore2dollarskuscore76) (+ 10 (+ t35uscore0dollarskuscore3 xuscore2dollarskuscore66)))))))
(check-sat)
(exit)
