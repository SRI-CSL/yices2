(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 5019 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore1 () Real)
(declare-fun t1uscore0dollarskuscore0 () Real)
(declare-fun yuscore2dollarskuscore1 () Real)
(declare-fun ts1uscore0 () Real)
(assert (not (exists ((ts1uscore0 Real)) (=> (and (and (and (and (and (=> (and (<= 0 ts1uscore0) (<= ts1uscore0 t1uscore0dollarskuscore0)) (<= (+ ts1uscore0 yuscore2dollarskuscore1) 10)) (>= t1uscore0dollarskuscore0 0)) (< yuscore2dollarskuscore1 10)) (= stuscore2dollarskuscore1 0)) (>= yuscore2dollarskuscore1 1)) (<= yuscore2dollarskuscore1 12)) (or (or (= stuscore2dollarskuscore1 1) (= stuscore2dollarskuscore1 3)) (>= (+ t1uscore0dollarskuscore0 yuscore2dollarskuscore1) 1))))))
(check-sat)
(exit)
