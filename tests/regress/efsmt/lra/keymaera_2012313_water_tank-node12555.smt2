(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 12555 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts10uscore0 () Real)
(declare-fun stuscore2dollarskuscore17 () Real)
(declare-fun xuscore2dollarskuscore9 () Real)
(declare-fun t10uscore0dollarskuscore0 () Real)
(declare-fun yuscore2dollarskuscore17 () Real)
(assert (not (exists ((ts10uscore0 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts10uscore0) (<= ts10uscore0 t10uscore0dollarskuscore0)) (<= (+ ts10uscore0 xuscore2dollarskuscore9) 2)) (>= t10uscore0dollarskuscore0 0)) (> xuscore2dollarskuscore9 2)) (= stuscore2dollarskuscore17 1)) (>= yuscore2dollarskuscore17 1)) (<= yuscore2dollarskuscore17 12)) (<= yuscore2dollarskuscore17 (+ 10 xuscore2dollarskuscore9))) (or (= stuscore2dollarskuscore17 3) (>= (+ t10uscore0dollarskuscore0 yuscore2dollarskuscore17) 1))))))
(check-sat)
(exit)
