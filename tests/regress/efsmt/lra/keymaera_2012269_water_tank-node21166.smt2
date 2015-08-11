(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 21166 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore31 () Real)
(declare-fun stuscore2dollarskuscore39 () Real)
(declare-fun ts22uscore2 () Real)
(declare-fun t22uscore0dollarskuscore2 () Real)
(declare-fun yuscore2dollarskuscore39 () Real)
(assert (not (exists ((ts22uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore31))) (=> (and (and (and (and (and (and (=> (and (<= 0 ts22uscore2) (<= ts22uscore2 t22uscore0dollarskuscore2)) (<= (+ ts22uscore2 xuscore2dollarskuscore31) 2)) (>= t22uscore0dollarskuscore2 0)) (< xuscore2dollarskuscore31 2)) (= stuscore2dollarskuscore39 3)) (>= yuscore2dollarskuscore39 1)) (<= yuscore2dollarskuscore39 12)) (>= yuscore2dollarskuscore39 (- 5 ?v_0))) (or (= stuscore2dollarskuscore39 1) (>= (+ (* (- 2) t22uscore0dollarskuscore2) yuscore2dollarskuscore39) (- 5 (+ (* 2 t22uscore0dollarskuscore2) ?v_0)))))))))
(check-sat)
(exit)
