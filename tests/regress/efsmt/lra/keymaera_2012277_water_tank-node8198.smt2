(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 8198 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts4uscore0 () Real)
(declare-fun yuscore2dollarskuscore6 () Real)
(declare-fun t4uscore0dollarskuscore0 () Real)
(declare-fun stuscore2dollarskuscore6 () Real)
(assert (not (exists ((ts4uscore0 Real)) (=> (and (and (and (and (and (=> (and (<= 0 ts4uscore0) (<= ts4uscore0 t4uscore0dollarskuscore0)) (>= (+ (* (- 2) ts4uscore0) yuscore2dollarskuscore6) 5)) (>= t4uscore0dollarskuscore0 0)) (< yuscore2dollarskuscore6 5)) (= stuscore2dollarskuscore6 2)) (>= yuscore2dollarskuscore6 1)) (<= yuscore2dollarskuscore6 12)) (or (or (= stuscore2dollarskuscore6 1) (= stuscore2dollarskuscore6 3)) (>= (+ (* (- 2) t4uscore0dollarskuscore0) yuscore2dollarskuscore6) 1))))))
(check-sat)
(exit)
