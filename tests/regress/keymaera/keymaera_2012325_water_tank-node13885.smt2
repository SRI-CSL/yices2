(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 13885 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore14 () Real)
(declare-fun ts12uscore2 () Real)
(declare-fun yuscore2dollarskuscore22 () Real)
(declare-fun stuscore2dollarskuscore22 () Real)
(declare-fun t12uscore0dollarskuscore2 () Real)
(assert (not (exists ((ts12uscore2 Real)) (=> (and (and (and (and (and (and (and (= stuscore2dollarskuscore22 1) (=> (and (<= 0 ts12uscore2) (<= ts12uscore2 t12uscore0dollarskuscore2)) (>= (+ (* (- 2) ts12uscore2) yuscore2dollarskuscore22) 5))) (>= t12uscore0dollarskuscore2 0)) (> yuscore2dollarskuscore22 5)) (= stuscore2dollarskuscore22 2)) (>= yuscore2dollarskuscore22 1)) (<= yuscore2dollarskuscore22 12)) (<= yuscore2dollarskuscore22 (+ 10 xuscore2dollarskuscore14))) (or (= stuscore2dollarskuscore22 3) (<= (+ (* (- 2) t12uscore0dollarskuscore2) yuscore2dollarskuscore22) (+ 10 (+ t12uscore0dollarskuscore2 xuscore2dollarskuscore14))))))))
(check-sat)
(exit)
