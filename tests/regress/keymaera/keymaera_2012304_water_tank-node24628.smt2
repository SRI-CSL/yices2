(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 24628 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t27uscore0dollarskuscore2 () Real)
(declare-fun ts27uscore2 () Real)
(declare-fun xuscore2dollarskuscore44 () Real)
(declare-fun stuscore2dollarskuscore52 () Real)
(declare-fun yuscore2dollarskuscore52 () Real)
(assert (not (exists ((ts27uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore44))) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore52 3) (=> (and (<= 0 ts27uscore2) (<= ts27uscore2 t27uscore0dollarskuscore2)) (>= (+ (* (- 2) ts27uscore2) yuscore2dollarskuscore52) 5))) (>= t27uscore0dollarskuscore2 0)) (> yuscore2dollarskuscore52 5)) (= stuscore2dollarskuscore52 2)) (>= yuscore2dollarskuscore52 1)) (<= yuscore2dollarskuscore52 12)) (>= yuscore2dollarskuscore52 (- 5 ?v_0))) (<= yuscore2dollarskuscore52 (+ 10 xuscore2dollarskuscore44))) (>= (+ (* (- 2) t27uscore0dollarskuscore2) yuscore2dollarskuscore52) (- 5 (+ (* 2 t27uscore0dollarskuscore2) ?v_0))))))))
(check-sat)
(exit)
