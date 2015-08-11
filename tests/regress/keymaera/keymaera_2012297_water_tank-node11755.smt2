(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 11755 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts9uscore0 () Real)
(declare-fun xuscore2dollarskuscore6 () Real)
(declare-fun stuscore2dollarskuscore14 () Real)
(declare-fun yuscore2dollarskuscore14 () Real)
(declare-fun t9uscore0dollarskuscore0 () Real)
(assert (not (exists ((ts9uscore0 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts9uscore0) (<= ts9uscore0 t9uscore0dollarskuscore0)) (<= (+ ts9uscore0 xuscore2dollarskuscore6) 2)) (>= t9uscore0dollarskuscore0 0)) (< xuscore2dollarskuscore6 2)) (= stuscore2dollarskuscore14 1)) (>= yuscore2dollarskuscore14 1)) (<= yuscore2dollarskuscore14 12)) (<= yuscore2dollarskuscore14 (+ 10 xuscore2dollarskuscore6))) (or (= stuscore2dollarskuscore14 3) (>= (+ t9uscore0dollarskuscore0 yuscore2dollarskuscore14) 1))))))
(check-sat)
(exit)
