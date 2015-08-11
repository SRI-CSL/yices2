(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 21141 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore30 () Real)
(declare-fun ts22uscore1 () Real)
(declare-fun stuscore2dollarskuscore38 () Real)
(declare-fun yuscore2dollarskuscore38 () Real)
(declare-fun t22uscore0dollarskuscore1 () Real)
(assert (not (exists ((ts22uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts22uscore1) (<= ts22uscore1 t22uscore0dollarskuscore1)) (<= (+ ts22uscore1 xuscore2dollarskuscore30) 2)) (>= t22uscore0dollarskuscore1 0)) (< xuscore2dollarskuscore30 2)) (= stuscore2dollarskuscore38 3)) (>= yuscore2dollarskuscore38 1)) (<= yuscore2dollarskuscore38 12)) (>= yuscore2dollarskuscore38 (- 5 (* 2 xuscore2dollarskuscore30)))) (or (= stuscore2dollarskuscore38 1) (<= (+ (* (- 2) t22uscore0dollarskuscore1) yuscore2dollarskuscore38) 12))))))
(check-sat)
(exit)
