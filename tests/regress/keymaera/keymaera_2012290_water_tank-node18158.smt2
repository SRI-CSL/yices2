(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 18158 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts18uscore1 () Real)
(declare-fun yuscore2dollarskuscore32 () Real)
(declare-fun t18uscore0dollarskuscore1 () Real)
(declare-fun xuscore2dollarskuscore24 () Real)
(declare-fun stuscore2dollarskuscore32 () Real)
(assert (not (exists ((ts18uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts18uscore1) (<= ts18uscore1 t18uscore0dollarskuscore1)) (>= (+ (* (- 2) ts18uscore1) yuscore2dollarskuscore32) 5)) (>= t18uscore0dollarskuscore1 0)) (> yuscore2dollarskuscore32 5)) (= stuscore2dollarskuscore32 2)) (>= yuscore2dollarskuscore32 1)) (<= yuscore2dollarskuscore32 12)) (>= yuscore2dollarskuscore32 (- 5 (* 2 xuscore2dollarskuscore24)))) (or (= stuscore2dollarskuscore32 1) (<= (+ (* (- 2) t18uscore0dollarskuscore1) yuscore2dollarskuscore32) 12))))))
(check-sat)
(exit)
