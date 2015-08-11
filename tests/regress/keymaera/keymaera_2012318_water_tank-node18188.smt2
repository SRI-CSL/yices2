(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 18188 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts18uscore2 () Real)
(declare-fun yuscore2dollarskuscore33 () Real)
(declare-fun xuscore2dollarskuscore25 () Real)
(declare-fun t18uscore0dollarskuscore2 () Real)
(declare-fun stuscore2dollarskuscore33 () Real)
(assert (not (exists ((ts18uscore2 Real)) (let ((?v_0 (* 2 xuscore2dollarskuscore25))) (=> (and (and (and (and (and (and (and (= stuscore2dollarskuscore33 3) (=> (and (<= 0 ts18uscore2) (<= ts18uscore2 t18uscore0dollarskuscore2)) (>= (+ (* (- 2) ts18uscore2) yuscore2dollarskuscore33) 5))) (>= t18uscore0dollarskuscore2 0)) (> yuscore2dollarskuscore33 5)) (= stuscore2dollarskuscore33 2)) (>= yuscore2dollarskuscore33 1)) (<= yuscore2dollarskuscore33 12)) (>= yuscore2dollarskuscore33 (- 5 ?v_0))) (or (= stuscore2dollarskuscore33 1) (>= (+ (* (- 2) t18uscore0dollarskuscore2) yuscore2dollarskuscore33) (- 5 (+ (* 2 t18uscore0dollarskuscore2) ?v_0)))))))))
(check-sat)
(exit)
