(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 29317 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore72 () Real)
(declare-fun xuscore2dollarskuscore62 () Real)
(declare-fun yuscore2dollarskuscore72 () Real)
(declare-fun t21uscore0dollarskuscore2 () Real)
(declare-fun ts21uscore2 () Real)
(assert (not (exists ((ts21uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore62))) (=> (and (and (and (and (and (and (=> (and (<= 0 ts21uscore2) (<= ts21uscore2 t21uscore0dollarskuscore2)) (<= (+ ts21uscore2 xuscore2dollarskuscore62) 2)) (>= t21uscore0dollarskuscore2 0)) (> xuscore2dollarskuscore62 2)) (= stuscore2dollarskuscore72 3)) (>= yuscore2dollarskuscore72 1)) (<= yuscore2dollarskuscore72 12)) (>= yuscore2dollarskuscore72 (- 5 ?v_0))) (or (= stuscore2dollarskuscore72 1) (>= (+ (* (- 2) t21uscore0dollarskuscore2) yuscore2dollarskuscore72) (- 5 (+ (* 2 t21uscore0dollarskuscore2) ?v_0)))))))))
(check-sat)
(exit)
