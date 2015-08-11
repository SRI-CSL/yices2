(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 27654 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t31uscore0dollarskuscore1 () Real)
(declare-fun ts31uscore1 () Real)
(declare-fun yuscore2dollarskuscore60 () Real)
(declare-fun stuscore2dollarskuscore60 () Real)
(declare-fun xuscore2dollarskuscore52 () Real)
(assert (not (exists ((ts31uscore1 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts31uscore1) (<= ts31uscore1 t31uscore0dollarskuscore1)) (<= (+ ts31uscore1 xuscore2dollarskuscore52) 2)) (>= t31uscore0dollarskuscore1 0)) (< xuscore2dollarskuscore52 2)) (= stuscore2dollarskuscore60 3)) (>= yuscore2dollarskuscore60 1)) (<= yuscore2dollarskuscore60 12)) (>= yuscore2dollarskuscore60 (- 5 (* 2 xuscore2dollarskuscore52)))) (<= yuscore2dollarskuscore60 (+ 10 xuscore2dollarskuscore52))) (<= (+ (* (- 2) t31uscore0dollarskuscore1) yuscore2dollarskuscore60) 12)))))
(check-sat)
(exit)
