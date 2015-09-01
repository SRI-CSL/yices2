(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 14909 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun xuscore2dollarskuscore17 () Real)
(declare-fun ts13uscore2 () Real)
(declare-fun yuscore2dollarskuscore25 () Real)
(declare-fun stuscore2dollarskuscore25 () Real)
(declare-fun t13uscore0dollarskuscore2 () Real)
(assert (not (exists ((ts13uscore2 Real)) (=> (and (and (and (and (and (and (and (= stuscore2dollarskuscore25 1) (=> (and (<= 0 ts13uscore2) (<= ts13uscore2 t13uscore0dollarskuscore2)) (>= (+ (* (- 2) ts13uscore2) yuscore2dollarskuscore25) 5))) (>= t13uscore0dollarskuscore2 0)) (< yuscore2dollarskuscore25 5)) (= stuscore2dollarskuscore25 2)) (>= yuscore2dollarskuscore25 1)) (<= yuscore2dollarskuscore25 12)) (<= yuscore2dollarskuscore25 (+ 10 xuscore2dollarskuscore17))) (or (= stuscore2dollarskuscore25 3) (<= (+ (* (- 2) t13uscore0dollarskuscore2) yuscore2dollarskuscore25) (+ 10 (+ t13uscore0dollarskuscore2 xuscore2dollarskuscore17))))))))
(check-sat)
(exit)
