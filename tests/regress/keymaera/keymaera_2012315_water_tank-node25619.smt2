(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 25619 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts28uscore1 () Real)
(declare-fun yuscore2dollarskuscore55 () Real)
(declare-fun xuscore2dollarskuscore47 () Real)
(declare-fun t28uscore0dollarskuscore1 () Real)
(declare-fun stuscore2dollarskuscore55 () Real)
(assert (not (exists ((ts28uscore1 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts28uscore1) (<= ts28uscore1 t28uscore0dollarskuscore1)) (>= (+ (* (- 2) ts28uscore1) yuscore2dollarskuscore55) 5)) (>= t28uscore0dollarskuscore1 0)) (< yuscore2dollarskuscore55 5)) (= stuscore2dollarskuscore55 2)) (>= yuscore2dollarskuscore55 1)) (<= yuscore2dollarskuscore55 12)) (>= yuscore2dollarskuscore55 (- 5 (* 2 xuscore2dollarskuscore47)))) (<= yuscore2dollarskuscore55 (+ 10 xuscore2dollarskuscore47))) (<= (+ (* (- 2) t28uscore0dollarskuscore1) yuscore2dollarskuscore55) 12)))))
(check-sat)
(exit)
