(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 9351 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore1 () Real)
(declare-fun yuscore2dollarskuscore9 () Real)
(declare-fun t6uscore0dollarskuscore1 () Real)
(declare-fun ts6uscore1 () Real)
(declare-fun stuscore2dollarskuscore9 () Real)
(assert (not (exists ((ts6uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts6uscore1) (<= ts6uscore1 t6uscore0dollarskuscore1)) (<= (+ ts6uscore1 yuscore2dollarskuscore9) 10)) (>= t6uscore0dollarskuscore1 0)) (< yuscore2dollarskuscore9 10)) (= stuscore2dollarskuscore9 0)) (>= yuscore2dollarskuscore9 1)) (<= yuscore2dollarskuscore9 12)) (<= yuscore2dollarskuscore9 (+ 10 xuscore2dollarskuscore1))) (or (= stuscore2dollarskuscore9 3) (<= (+ t6uscore0dollarskuscore1 yuscore2dollarskuscore9) 12))))))
(check-sat)
(exit)
