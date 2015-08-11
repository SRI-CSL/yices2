(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 9381 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun yuscore2dollarskuscore10 () Real)
(declare-fun xuscore2dollarskuscore2 () Real)
(declare-fun stuscore2dollarskuscore10 () Real)
(declare-fun ts6uscore2 () Real)
(declare-fun t6uscore0dollarskuscore2 () Real)
(assert (not (exists ((ts6uscore2 Real)) (=> (and (and (and (and (and (and (and (= stuscore2dollarskuscore10 1) (=> (and (<= 0 ts6uscore2) (<= ts6uscore2 t6uscore0dollarskuscore2)) (<= (+ ts6uscore2 yuscore2dollarskuscore10) 10))) (>= t6uscore0dollarskuscore2 0)) (< yuscore2dollarskuscore10 10)) (= stuscore2dollarskuscore10 0)) (>= yuscore2dollarskuscore10 1)) (<= yuscore2dollarskuscore10 12)) (<= yuscore2dollarskuscore10 (+ 10 xuscore2dollarskuscore2))) (or (= stuscore2dollarskuscore10 3) (<= (+ t6uscore0dollarskuscore2 yuscore2dollarskuscore10) (+ 10 (+ t6uscore0dollarskuscore2 xuscore2dollarskuscore2))))))))
(check-sat)
(exit)
