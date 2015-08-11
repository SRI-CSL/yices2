(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 28794 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t16uscore0dollarskuscore1 () Real)
(declare-fun xuscore2dollarskuscore58 () Real)
(declare-fun stuscore2dollarskuscore68 () Real)
(declare-fun yuscore2dollarskuscore68 () Real)
(declare-fun ts16uscore1 () Real)
(assert (not (exists ((ts16uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts16uscore1) (<= ts16uscore1 t16uscore0dollarskuscore1)) (<= (+ ts16uscore1 yuscore2dollarskuscore68) 10)) (>= t16uscore0dollarskuscore1 0)) (> yuscore2dollarskuscore68 10)) (= stuscore2dollarskuscore68 0)) (>= yuscore2dollarskuscore68 1)) (<= yuscore2dollarskuscore68 12)) (>= yuscore2dollarskuscore68 (- 5 (* 2 xuscore2dollarskuscore58)))) (or (= stuscore2dollarskuscore68 1) (<= (+ t16uscore0dollarskuscore1 yuscore2dollarskuscore68) 12))))))
(check-sat)
(exit)
