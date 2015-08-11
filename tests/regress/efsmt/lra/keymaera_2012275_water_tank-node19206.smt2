(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 19206 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts19uscore2 () Real)
(declare-fun xuscore2dollarskuscore28 () Real)
(declare-fun stuscore2dollarskuscore36 () Real)
(declare-fun yuscore2dollarskuscore36 () Real)
(declare-fun t19uscore0dollarskuscore2 () Real)
(assert (not (exists ((ts19uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore28))) (=> (and (and (and (and (and (and (and (= stuscore2dollarskuscore36 3) (=> (and (<= 0 ts19uscore2) (<= ts19uscore2 t19uscore0dollarskuscore2)) (>= (+ (* (- 2) ts19uscore2) yuscore2dollarskuscore36) 5))) (>= t19uscore0dollarskuscore2 0)) (< yuscore2dollarskuscore36 5)) (= stuscore2dollarskuscore36 2)) (>= yuscore2dollarskuscore36 1)) (<= yuscore2dollarskuscore36 12)) (>= yuscore2dollarskuscore36 (- 5 ?v_0))) (or (= stuscore2dollarskuscore36 1) (>= (+ (* (- 2) t19uscore0dollarskuscore2) yuscore2dollarskuscore36) (- 5 (+ (* 2 t19uscore0dollarskuscore2) ?v_0)))))))))
(check-sat)
(exit)
