(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 30133 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore75 () Real)
(declare-fun xuscore2dollarskuscore65 () Real)
(declare-fun t35uscore0dollarskuscore2 () Real)
(declare-fun ts35uscore2 () Real)
(declare-fun yuscore2dollarskuscore75 () Real)
(assert (not (exists ((ts35uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore65))) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore75 3) (=> (and (<= 0 ts35uscore2) (<= ts35uscore2 t35uscore0dollarskuscore2)) (<= (+ ts35uscore2 xuscore2dollarskuscore65) 2))) (>= t35uscore0dollarskuscore2 0)) (< xuscore2dollarskuscore65 2)) (= stuscore2dollarskuscore75 1)) (>= yuscore2dollarskuscore75 1)) (<= yuscore2dollarskuscore75 12)) (>= yuscore2dollarskuscore75 (- 5 ?v_0))) (<= yuscore2dollarskuscore75 (+ 10 xuscore2dollarskuscore65))) (>= (+ t35uscore0dollarskuscore2 yuscore2dollarskuscore75) (- 5 (+ (* 2 t35uscore0dollarskuscore2) ?v_0))))))))
(check-sat)
(exit)
