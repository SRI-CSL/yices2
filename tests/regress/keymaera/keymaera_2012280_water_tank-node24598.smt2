(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 24598 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t27uscore0dollarskuscore1 () Real)
(declare-fun ts27uscore1 () Real)
(declare-fun xuscore2dollarskuscore43 () Real)
(declare-fun stuscore2dollarskuscore51 () Real)
(declare-fun yuscore2dollarskuscore51 () Real)
(assert (not (exists ((ts27uscore1 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts27uscore1) (<= ts27uscore1 t27uscore0dollarskuscore1)) (>= (+ (* (- 2) ts27uscore1) yuscore2dollarskuscore51) 5)) (>= t27uscore0dollarskuscore1 0)) (> yuscore2dollarskuscore51 5)) (= stuscore2dollarskuscore51 2)) (>= yuscore2dollarskuscore51 1)) (<= yuscore2dollarskuscore51 12)) (>= yuscore2dollarskuscore51 (- 5 (* 2 xuscore2dollarskuscore43)))) (<= yuscore2dollarskuscore51 (+ 10 xuscore2dollarskuscore43))) (<= (+ (* (- 2) t27uscore0dollarskuscore1) yuscore2dollarskuscore51) 12)))))
(check-sat)
(exit)
