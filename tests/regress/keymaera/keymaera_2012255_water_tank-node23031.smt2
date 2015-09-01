(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 23031 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts25uscore1 () Real)
(declare-fun t25uscore0dollarskuscore1 () Real)
(declare-fun stuscore2dollarskuscore46 () Real)
(declare-fun yuscore2dollarskuscore46 () Real)
(declare-fun xuscore2dollarskuscore38 () Real)
(assert (not (exists ((ts25uscore1 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts25uscore1) (<= ts25uscore1 t25uscore0dollarskuscore1)) (<= (+ ts25uscore1 yuscore2dollarskuscore46) 10)) (>= t25uscore0dollarskuscore1 0)) (> yuscore2dollarskuscore46 10)) (= stuscore2dollarskuscore46 0)) (>= yuscore2dollarskuscore46 1)) (<= yuscore2dollarskuscore46 12)) (>= yuscore2dollarskuscore46 (- 5 (* 2 xuscore2dollarskuscore38)))) (<= yuscore2dollarskuscore46 (+ 10 xuscore2dollarskuscore38))) (<= (+ t25uscore0dollarskuscore1 yuscore2dollarskuscore46) 12)))))
(check-sat)
(exit)
