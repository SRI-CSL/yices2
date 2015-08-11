(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 30870 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts30uscore2 () Real)
(declare-fun t30uscore0dollarskuscore2 () Real)
(declare-fun stuscore2dollarskuscore78 () Real)
(declare-fun yuscore2dollarskuscore78 () Real)
(declare-fun xuscore2dollarskuscore68 () Real)
(assert (not (exists ((ts30uscore2 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts30uscore2) (<= ts30uscore2 t30uscore0dollarskuscore2)) (<= (+ ts30uscore2 xuscore2dollarskuscore68) 2)) (>= t30uscore0dollarskuscore2 0)) (> xuscore2dollarskuscore68 2)) (= stuscore2dollarskuscore78 3)) (>= yuscore2dollarskuscore78 1)) (<= yuscore2dollarskuscore78 12)) (>= yuscore2dollarskuscore78 (- 5 (* 2 xuscore2dollarskuscore68)))) (<= yuscore2dollarskuscore78 (+ 10 xuscore2dollarskuscore68))) (<= (+ (* (- 2) t30uscore0dollarskuscore2) yuscore2dollarskuscore78) 12)))))
(check-sat)
(exit)
