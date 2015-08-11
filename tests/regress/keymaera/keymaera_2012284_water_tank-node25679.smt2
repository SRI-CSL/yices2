(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 25679 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun t28uscore0dollarskuscore3 () Real)
(declare-fun xuscore2dollarskuscore49 () Real)
(declare-fun ts28uscore3 () Real)
(declare-fun yuscore2dollarskuscore57 () Real)
(declare-fun stuscore2dollarskuscore57 () Real)
(assert (not (exists ((ts28uscore3 Real)) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore57 1) (=> (and (<= 0 ts28uscore3) (<= ts28uscore3 t28uscore0dollarskuscore3)) (>= (+ (* (- 2) ts28uscore3) yuscore2dollarskuscore57) 5))) (>= t28uscore0dollarskuscore3 0)) (< yuscore2dollarskuscore57 5)) (= stuscore2dollarskuscore57 2)) (>= yuscore2dollarskuscore57 1)) (<= yuscore2dollarskuscore57 12)) (>= yuscore2dollarskuscore57 (- 5 (* 2 xuscore2dollarskuscore49)))) (<= yuscore2dollarskuscore57 (+ 10 xuscore2dollarskuscore49))) (<= (+ (* (- 2) t28uscore0dollarskuscore3) yuscore2dollarskuscore57) (+ 10 (+ t28uscore0dollarskuscore3 xuscore2dollarskuscore49)))))))
(check-sat)
(exit)
