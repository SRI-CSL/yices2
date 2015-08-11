(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 29292 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore71 () Real)
(declare-fun xuscore2dollarskuscore61 () Real)
(declare-fun yuscore2dollarskuscore71 () Real)
(declare-fun t21uscore0dollarskuscore1 () Real)
(declare-fun ts21uscore1 () Real)
(assert (not (exists ((ts21uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts21uscore1) (<= ts21uscore1 t21uscore0dollarskuscore1)) (<= (+ ts21uscore1 xuscore2dollarskuscore61) 2)) (>= t21uscore0dollarskuscore1 0)) (> xuscore2dollarskuscore61 2)) (= stuscore2dollarskuscore71 3)) (>= yuscore2dollarskuscore71 1)) (<= yuscore2dollarskuscore71 12)) (>= yuscore2dollarskuscore71 (- 5 (* 2 xuscore2dollarskuscore61)))) (or (= stuscore2dollarskuscore71 1) (<= (+ (* (- 2) t21uscore0dollarskuscore1) yuscore2dollarskuscore71) 12))))))
(check-sat)
(exit)
