(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 31001 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t36uscore0dollarskuscore1 () Real)
(declare-fun yuscore2dollarskuscore81 () Real)
(declare-fun stuscore2dollarskuscore81 () Real)
(declare-fun xuscore2dollarskuscore71 () Real)
(declare-fun ts36uscore1 () Real)
(assert (not (exists ((ts36uscore1 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts36uscore1) (<= ts36uscore1 t36uscore0dollarskuscore1)) (<= (+ ts36uscore1 xuscore2dollarskuscore71) 2)) (>= t36uscore0dollarskuscore1 0)) (> xuscore2dollarskuscore71 2)) (= stuscore2dollarskuscore81 1)) (>= yuscore2dollarskuscore81 1)) (<= yuscore2dollarskuscore81 12)) (>= yuscore2dollarskuscore81 (- 5 (* 2 xuscore2dollarskuscore71)))) (<= yuscore2dollarskuscore81 (+ 10 xuscore2dollarskuscore71))) (<= (+ t36uscore0dollarskuscore1 yuscore2dollarskuscore81) 12)))))
(check-sat)
(exit)
