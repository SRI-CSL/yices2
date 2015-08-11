(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 26754 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore58 () Real)
(declare-fun t30uscore0dollarskuscore0 () Real)
(declare-fun xuscore2dollarskuscore50 () Real)
(declare-fun yuscore2dollarskuscore58 () Real)
(declare-fun ts30uscore0 () Real)
(assert (not (exists ((ts30uscore0 Real)) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore58 1) (=> (and (<= 0 ts30uscore0) (<= ts30uscore0 t30uscore0dollarskuscore0)) (<= (+ ts30uscore0 xuscore2dollarskuscore50) 2))) (>= t30uscore0dollarskuscore0 0)) (> xuscore2dollarskuscore50 2)) (= stuscore2dollarskuscore58 3)) (>= yuscore2dollarskuscore58 1)) (<= yuscore2dollarskuscore58 12)) (>= yuscore2dollarskuscore58 (- 5 (* 2 xuscore2dollarskuscore50)))) (<= yuscore2dollarskuscore58 (+ 10 xuscore2dollarskuscore50))) (<= (+ (* (- 2) t30uscore0dollarskuscore0) yuscore2dollarskuscore58) (+ 10 (+ t30uscore0dollarskuscore0 xuscore2dollarskuscore50)))))))
(check-sat)
(exit)
