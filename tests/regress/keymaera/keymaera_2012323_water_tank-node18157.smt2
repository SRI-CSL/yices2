(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 18157 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts18uscore0 () Real)
(declare-fun yuscore2dollarskuscore31 () Real)
(declare-fun xuscore2dollarskuscore23 () Real)
(declare-fun t18uscore0dollarskuscore0 () Real)
(declare-fun stuscore2dollarskuscore31 () Real)
(assert (not (exists ((ts18uscore0 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts18uscore0) (<= ts18uscore0 t18uscore0dollarskuscore0)) (>= (+ (* (- 2) ts18uscore0) yuscore2dollarskuscore31) 5)) (>= t18uscore0dollarskuscore0 0)) (> yuscore2dollarskuscore31 5)) (= stuscore2dollarskuscore31 2)) (>= yuscore2dollarskuscore31 1)) (<= yuscore2dollarskuscore31 12)) (>= yuscore2dollarskuscore31 (- 5 (* 2 xuscore2dollarskuscore23)))) (or (= stuscore2dollarskuscore31 1) (>= (+ (* (- 2) t18uscore0dollarskuscore0) yuscore2dollarskuscore31) 1))))))
(check-sat)
(exit)
