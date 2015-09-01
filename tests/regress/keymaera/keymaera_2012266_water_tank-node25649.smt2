(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 25649 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t28uscore0dollarskuscore2 () Real)
(declare-fun xuscore2dollarskuscore48 () Real)
(declare-fun yuscore2dollarskuscore56 () Real)
(declare-fun ts28uscore2 () Real)
(declare-fun stuscore2dollarskuscore56 () Real)
(assert (not (exists ((ts28uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore48))) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore56 3) (=> (and (<= 0 ts28uscore2) (<= ts28uscore2 t28uscore0dollarskuscore2)) (>= (+ (* (- 2) ts28uscore2) yuscore2dollarskuscore56) 5))) (>= t28uscore0dollarskuscore2 0)) (< yuscore2dollarskuscore56 5)) (= stuscore2dollarskuscore56 2)) (>= yuscore2dollarskuscore56 1)) (<= yuscore2dollarskuscore56 12)) (>= yuscore2dollarskuscore56 (- 5 ?v_0))) (<= yuscore2dollarskuscore56 (+ 10 xuscore2dollarskuscore48))) (>= (+ (* (- 2) t28uscore0dollarskuscore2) yuscore2dollarskuscore56) (- 5 (+ (* 2 t28uscore0dollarskuscore2) ?v_0))))))))
(check-sat)
(exit)
