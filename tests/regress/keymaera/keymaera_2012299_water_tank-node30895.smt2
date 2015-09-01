(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 30895 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts30uscore3 () Real)
(declare-fun stuscore2dollarskuscore79 () Real)
(declare-fun yuscore2dollarskuscore79 () Real)
(declare-fun xuscore2dollarskuscore69 () Real)
(declare-fun t30uscore0dollarskuscore3 () Real)
(assert (not (exists ((ts30uscore3 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore69))) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts30uscore3) (<= ts30uscore3 t30uscore0dollarskuscore3)) (<= (+ ts30uscore3 xuscore2dollarskuscore69) 2)) (>= t30uscore0dollarskuscore3 0)) (> xuscore2dollarskuscore69 2)) (= stuscore2dollarskuscore79 3)) (>= yuscore2dollarskuscore79 1)) (<= yuscore2dollarskuscore79 12)) (>= yuscore2dollarskuscore79 (- 5 ?v_0))) (<= yuscore2dollarskuscore79 (+ 10 xuscore2dollarskuscore69))) (>= (+ (* (- 2) t30uscore0dollarskuscore3) yuscore2dollarskuscore79) (- 5 (+ (* 2 t30uscore0dollarskuscore3) ?v_0))))))))
(check-sat)
(exit)
