(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 5020 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore2 () Real)
(declare-fun t1uscore0dollarskuscore1 () Real)
(declare-fun yuscore2dollarskuscore2 () Real)
(declare-fun ts1uscore1 () Real)
(assert (not (exists ((ts1uscore1 Real)) (=> (and (and (and (and (and (=> (and (<= 0 ts1uscore1) (<= ts1uscore1 t1uscore0dollarskuscore1)) (<= (+ ts1uscore1 yuscore2dollarskuscore2) 10)) (>= t1uscore0dollarskuscore1 0)) (< yuscore2dollarskuscore2 10)) (= stuscore2dollarskuscore2 0)) (>= yuscore2dollarskuscore2 1)) (<= yuscore2dollarskuscore2 12)) (or (or (= stuscore2dollarskuscore2 1) (= stuscore2dollarskuscore2 3)) (<= (+ t1uscore0dollarskuscore1 yuscore2dollarskuscore2) 12))))))
(check-sat)
(exit)
