(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 28519 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore63 () Real)
(declare-fun yuscore2dollarskuscore63 () Real)
(declare-fun t33uscore0dollarskuscore0 () Real)
(declare-fun ts33uscore0 () Real)
(assert (not (exists ((ts33uscore0 Real)) (=> (and (and (and (and (and (=> (and (<= 0 ts33uscore0) (<= ts33uscore0 t33uscore0dollarskuscore0)) (<= (+ ts33uscore0 yuscore2dollarskuscore63) 10)) (>= t33uscore0dollarskuscore0 0)) (> yuscore2dollarskuscore63 10)) (= stuscore2dollarskuscore63 0)) (>= yuscore2dollarskuscore63 1)) (<= yuscore2dollarskuscore63 12)) (or (or (= stuscore2dollarskuscore63 1) (= stuscore2dollarskuscore63 3)) (>= (+ t33uscore0dollarskuscore0 yuscore2dollarskuscore63) 1))))))
(check-sat)
(exit)
