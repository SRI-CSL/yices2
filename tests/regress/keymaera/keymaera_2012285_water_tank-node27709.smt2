(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 27709 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore54 () Real)
(declare-fun ts31uscore3 () Real)
(declare-fun yuscore2dollarskuscore62 () Real)
(declare-fun stuscore2dollarskuscore62 () Real)
(declare-fun t31uscore0dollarskuscore3 () Real)
(assert (not (exists ((ts31uscore3 Real)) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore62 1) (=> (and (<= 0 ts31uscore3) (<= ts31uscore3 t31uscore0dollarskuscore3)) (<= (+ ts31uscore3 xuscore2dollarskuscore54) 2))) (>= t31uscore0dollarskuscore3 0)) (< xuscore2dollarskuscore54 2)) (= stuscore2dollarskuscore62 3)) (>= yuscore2dollarskuscore62 1)) (<= yuscore2dollarskuscore62 12)) (>= yuscore2dollarskuscore62 (- 5 (* 2 xuscore2dollarskuscore54)))) (<= yuscore2dollarskuscore62 (+ 10 xuscore2dollarskuscore54))) (<= (+ (* (- 2) t31uscore0dollarskuscore3) yuscore2dollarskuscore62) (+ 10 (+ t31uscore0dollarskuscore3 xuscore2dollarskuscore54)))))))
(check-sat)
(exit)
