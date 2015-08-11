(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 23030 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t25uscore0dollarskuscore0 () Real)
(declare-fun ts25uscore0 () Real)
(declare-fun stuscore2dollarskuscore45 () Real)
(declare-fun yuscore2dollarskuscore45 () Real)
(declare-fun xuscore2dollarskuscore37 () Real)
(assert (not (exists ((ts25uscore0 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts25uscore0) (<= ts25uscore0 t25uscore0dollarskuscore0)) (<= (+ ts25uscore0 yuscore2dollarskuscore45) 10)) (>= t25uscore0dollarskuscore0 0)) (> yuscore2dollarskuscore45 10)) (= stuscore2dollarskuscore45 0)) (>= yuscore2dollarskuscore45 1)) (<= yuscore2dollarskuscore45 12)) (>= yuscore2dollarskuscore45 (- 5 (* 2 xuscore2dollarskuscore37)))) (<= yuscore2dollarskuscore45 (+ 10 xuscore2dollarskuscore37))) (>= (+ t25uscore0dollarskuscore0 yuscore2dollarskuscore45) 1)))))
(check-sat)
(exit)
